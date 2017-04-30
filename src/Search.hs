{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

module Search where

import Data.Foldable
import Prelude hiding (map)
import Control.Applicative
import Control.Arrow
import qualified Data.Set as S
import Relation
import TypeClasses
import Rel
import Prover

-- TODO: use the real thing
type DerivationTerm l a = DLSequent l a

{-

  1. Compute frontier
  2. Compute initial set of rules ---> initial sequents
  3. Put initial sequents in inactive set
  4. Pop inactive sequent. If no more, exit with failure
  5. Put popped inactive in active set
  6. Apply all rules to sequent
  7. Percolate
  8. Add resulting sequents that are not subsumed by old inactive sequents
     (taken from the so-called global index) to inactive set (forward
     subsumption)
  9. Remove inactive sequents that are subsumed by the new sequents (backward
     subsumption)
  10. Add rules to rule set
  11. If any new sequent subsumes the goal, exit
  12. Add new sequents to inactive set
  13. Goto 4

-}

-- doSearch
--   :: forall m a l.
--      ( Monad m
--      , HasProverState l a m
--      , HasProverEnvironment l a m
--      , Ord l
--      , Ord a
--      , Eq a
--      , Eq l
--      )
--   => m (Maybe (DerivationTerm l a))
-- doSearch = do
--   goal <- getGoal @l @a
--   let (initialSequents, initialRules) =
--         (S.toList *** id) . initialSequentsAndRules $ goal
--   addInactives (map initialIsBSChecked initialSequents)
--   addRules initialRules
--   (<|>) <$> (haveGoal (map initialIsFSChecked initialSequents)) <*> otterLoop

doSearch
  :: ( Monad m
     , HasProverState seqty m
     , HasProverEnvironment seqty m
     , Ord seqty
     , Eq seqty
     )
  => S.Set (SearchSequent 'Initial seqty) -> [Rule seqty] -> m (Maybe seqty)
doSearch initialSequents initialRules = do
  addInactives (map initialIsBSChecked initialList)
  addRules initialRules
  (<|>) <$> (haveGoal (map initialIsFSChecked initialList)) <*> otterLoop
  where
    initialList = S.toList initialSequents

otterLoop
  :: forall m seqty .
     ( Monad m
     , HasProverState seqty m
     , HasProverEnvironment seqty m
     , Ord seqty
     , Eq seqty
     )
  => m (Maybe seqty)
otterLoop = do
  inactive <- popInactive
  case inactive of
    Nothing -> return Nothing
    Just sequent -> do
      res <- processNewActive sequent
      unsubSeqs <- filterUnsubsumed (S.toList . resSequents $ res)
      unsubSeqs' <- removeSubsumedByAll unsubSeqs
      addInactives unsubSeqs'
      addRules (resRules res)
      (<|>) <$> (haveGoal unsubSeqs) <*> otterLoop

processNewActive
  :: (Monad m, HasProverState seqty m, Ord seqty)
  => ActiveSequent seqty -> m (RuleAppRes seqty)
processNewActive sequent = do
  actives <- getActives
  rules <- getRules
  let r1 = applyAll rules sequent
      r2 = percolate actives . resRules $ r1
  return $ r1 `mappend` r2

--------------------------------------------------------------------------------

-- | Result type of matching a list of rules to an input sequent.
type RuleAppRes seqty = (S.Set (ConclSequent seqty), [Rule seqty])

resSequents :: RuleAppRes seqty -> S.Set (ConclSequent seqty)
resSequents r = fst r

resRules :: RuleAppRes seqty -> [Rule seqty]
resRules r = snd r

partitionRuleRes
  :: (CanMap f, CanPartitionEithers f, Foldable f, Ord seqty)
  => f (RuleRes seqty) -> RuleAppRes seqty
partitionRuleRes =
  (S.fromList . toList *** toList) . partitionEithers . filterOut . map unRel

applyAll
  :: (Ord seqty, Foldable f, CanPartitionEithers f, CanMap f)
  => f (Rule seqty) -> ActiveSequent seqty -> RuleAppRes seqty
applyAll rules as = partitionRuleRes . map ($ as) $ rules

applyToActives
  :: (Ord seqty, Foldable f)
  => ActiveSequents seqty -> f (Rule seqty) -> RuleAppRes seqty
applyToActives actives rules = partitionRuleRes $ concatMap mapper rules
  where
    mapper rule = foldActives (foldMap (pure . applyRule rule)) actives

percolate
  :: (Ord seqty, Foldable f)
  => ActiveSequents seqty -> f (Rule seqty) -> RuleAppRes seqty
percolate actives rules = r1 `mappend` r2
  where
    r1 = applyToActives actives rules
    r2 = percolate actives . resRules $ r1
