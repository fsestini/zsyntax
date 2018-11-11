{-# LANGUAGE DataKinds #-}

module Otter.Internal.Search where

import Data.Bifunctor (second)
import Data.Maybe
import Control.Monad.State.Lazy
import Data.Foldable
import Control.Applicative

import Otter.Rule
import Otter.Internal.Structures
import Otter.SearchRes

data ProverState n = PS
  { _rules :: [SearchProperRule n]
  , _actives :: ActiveNodes n
  , _inactives :: InactiveNodes n
  , _index :: GlobalIndex n
  , _isGoal :: n -> Bool
  }

type Prover s g a = State (ProverState s) a

-- | Result type of matching a list of rules to an input sequent.
type RuleAppRes n = ([ConclNode n], [SearchProperRule n])

popInactive :: Prover s g (Maybe (ActiveNode s))
popInactive = do
  (PS r as is gi g) <- get
  case popInactiveOp is of
    Just (newIs, inactive) -> do
      let (newAs, active) = activate as inactive
      put (PS r newAs newIs gi g)
      return (Just active)
    Nothing -> return Nothing

getActives :: Prover s g (ActiveNodes s)
getActives = _actives <$> get

getRules :: Prover s g [SearchProperRule s]
getRules = _rules <$> get

isGoalM :: FSCheckedNode s -> Prover s g (Maybe (FSCheckedNode s))
isGoalM s = do
  g <- fmap _isGoal get
  if g (extractNode s) then pure (Just s) else pure Nothing

haveGoal :: [FSCheckedNode s] -> Prover s g (Maybe (FSCheckedNode s))
haveGoal = fmap (foldr (<|>) mzero) . mapM isGoalM

filterUnsubsumed
  :: Subsumable s
  => [ConclNode s] -> Prover s g [SearchNode FSChecked s]
filterUnsubsumed = fmap catMaybes . mapM isNotFwdSubsumed

isNotFwdSubsumed
  :: Subsumable s
  => ConclNode s -> Prover s g (Maybe (SearchNode FSChecked s))
isNotFwdSubsumed concl = fmap (flip fwdSubsumes concl . _index) get

removeSubsumedBy
  :: Subsumable s
  => SearchNode FSChecked s -> Prover s g (SearchNode BSChecked s)
removeSubsumedBy fschecked = do
  (PS r as is gi g) <- get
  let (newIs, bschecked) = removeSubsumedByOp fschecked is
  put (PS r as newIs gi g)
  return bschecked

addRule :: SearchProperRule s -> Prover s g ()
addRule r = do
  (PS rls as is gi g) <- get
  put (PS (r : rls) as is gi g)

addInactive :: SearchNode BSChecked s -> Prover s g ()
addInactive i = do
  (PS r as is gi g) <- get
  let (newIs, newInd) = addToInactives is gi i
  put (PS r as newIs newInd g)

percolate :: ActiveNodes s -> [SearchProperRule s] -> RuleAppRes s
percolate _ [] = mempty
percolate actives rules = r1 `mappend` r2
  where
    activeList = foldActives toList actives
    r1 = foldMap (uncurry apply) ((,) <$> rules <*> activeList)
    r2 = percolate actives . snd $ r1

processNewActive :: ActiveNode s -> Prover s g (RuleAppRes s)
processNewActive node = do
  actives <- getActives
  rules <- getRules
  let r1 = foldMap (`apply` node) rules
      r2 = percolate actives . snd $ r1
  return $ r1 <> r2

merge :: Maybe (SearchNode s a) -> SearchRes a -> SearchRes a
merge m sr = maybe (delay sr) (\x -> cons (extractNode x) sr) m

loop :: Subsumable s => Prover s g (SearchRes s)
loop = do
  inactive <- popInactive
  case inactive of
    Nothing -> pure []
    Just node -> do
      res <- processNewActive node
      unsubSeqs <- filterUnsubsumed (fst res)
      unsubSeqs' <- mapM removeSubsumedBy unsubSeqs
      mapM_ addInactive unsubSeqs'
      mapM_ addRule (snd res)
      liftM2 merge (haveGoal unsubSeqs) loop

doSearch
  :: Subsumable s
  => [SearchNode Initial s] -> [SearchProperRule s] -> Prover s g (SearchRes s)
doSearch initSeqs initRls = do
  mapM_ addInactive (fmap initIsBSCheckd initSeqs)
  mapM_ addRule initRls
  liftM2 merge (haveGoal (fmap initIsFSCheckd initSeqs)) loop

search
  :: Subsumable s
  => [s] -> [s -> Rule s s] -> (s -> Bool) -> (SearchRes s, [s])
search initial rls isGl = second (toList . _index) $
  runState
    (doSearch (fmap initialize initial) (fmap toProperRule rls))
    (PS [] emptyActives emptyInactives emptyGI isGl)
