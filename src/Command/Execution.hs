{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}

module Command.Execution where

import qualified Data.List.NonEmpty as NE
import Data.List.Split (splitOn)
import Data.List
import Data.Char

import Context
import TypeClasses (PickMonad(..))
import qualified Data.Set as S
import Relation
import SFormula
import Parser
import RelFormula
import Checking
import Data.Bifunctor
import Control.Monad.Trans.State.Strict hiding (get, put)
import Control.Monad.State.Class
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Free
import Control.Monad.Trans
import Prover
import Frontier
import DerivationTerm
import Control.Applicative (Alternative(..))
import Control.Monad.Trans.Except
import Data.Foldable (toList)

import Command.Structures

type Labels = Int
type Terms a = SimpleDerTerm a

--------------------------------------------------------------------------------
-- Single command execution

type EUI a = ExceptT String (Free UIF) a

toUI :: a -> EUI a -> UI a
toUI x = (>>= either ((>> return x) . logUI) return) . runExceptT

toUI' :: (String -> UI b) -> (a -> UI b) -> EUI a -> UI b
toUI' f g = (>>= either f g) . runExceptT

toEUI :: UI a -> EUI a
toEUI m = ExceptT (fmap Right m)

liftParse :: Either String a -> EUI a
liftParse = ExceptT . return . (first ("parse error: " ++))

liftSR :: SearchRes a -> EUI a
liftSR (OkRes x) = return x
liftSR Saturated = ExceptT . return . Left $ "not provable: not a theorem"
liftSR ThresholdBreak =
  ExceptT . return . Left $ "not provable: search space too big"

adjoinMsgEUI :: String -> EUI a -> EUI a
adjoinMsgEUI str = ExceptT . fmap (adjoinMsgE str) . runExceptT

adjoinMsgE :: String -> Either String a -> Either String a
adjoinMsgE str = first (str ++)

tryInsertTheorem
  :: ThrmName
  -> (QueriedSeq axlr fr, Either (SAxiom cty a) (SFormula eb cty a))
  -> ThrmEnv axlr fr eb cty a
  -> EUI (ThrmEnv axlr fr eb cty a)
tryInsertTheorem nm@(TN name) (q, frml) thrms =
  maybe (throwE msg >> return thrms) return newThrms
  where
    newThrms = feInsert nm (q, Just frml) thrms
    msg = "theorem named '" ++ name ++ "' already present"

tryInsertAxiom :: ThrmName
               -> (AddedAxiom axr ctr, SAxiom cty a)
               -> (AxEnv axr ctr cty a)
               -> EUI (AxEnv axr ctr cty a)
tryInsertAxiom name@(TN nm) axiom env =
  maybe (throwE msg) return (feInsert name axiom env)
  where
    msg = "axiom named '" ++ nm ++ "' already present"

addAxiom
  :: ReprAx axr ctr cty a
  => (AxEnv axr ctr cty a)
  -> ThrmName
  -> ctr
  -> axr
  -> axr
  -> UI (AxEnv axr ctr cty a)
addAxiom env name@(TN nm) ctrlset strFrom strTo =
  case (reprAx strFrom ctrlset strTo) of
    Left err -> (logUI $ "parse error: " ++ (show err)) >> return env
    Right axiom ->
      case feInsert name (AAx strFrom ctrlset strTo, axiom) env of
        Just newEnv -> return newEnv
        Nothing ->
          logUI ("Axiom named '" ++ nm ++ "' already present") >> return env

-- TODO: Ensure that lc is non-empty
fromNS
  :: (ElemBase eb a)
  => NeutralSequent eb cty a l -> Either (SAxiom cty a) (SFormula eb cty a)
fromNS (NS _ lc cs concl@(OLF conclF)) =
  maybe (Right (sImpl lcf mempty cs (fromLFormula conclF))) Left $ do
    from <- decideSF lcf
    to <- decideOLF concl
    return $ sAx from (fmap (const ()) to) cs
  where
    lcf = foldr1 sConj (fmap fromNF (toList lc))
    decideSF :: SFormula eb cs a -> Maybe (BSFormula cs a)
    decideSF (SF olf) = decideOLF olf

addTheorem
  :: forall a eb cty axlr fr axr ctr.
     ( Show a
     , ElemBase eb a
     , Ord a
     , Ord (eb a)
     , Ord (cty a)
     , BaseCtrl eb cty a
     , ReprAxList axlr
     , ReprFrml fr a
     )
  => (AxEnv axr ctr cty a)
  -> ThrmEnv axlr fr eb cty a
  -> ThrmName
  -> (QueriedSeq axlr fr)
  -> Free UIF (ThrmEnv axlr fr eb cty a)
addTheorem env thrms nm q =
  flip (toUI' ((>> return thrms) . logUI)) res $ \(impls, newThrms) -> do
    logUI ("provable with " ++ (show . length $ impls) ++ " transitions")
    forM_ impls (logUI . shower)
    return newThrms
  where
    shower :: (SFormula U U a, SFormula U U a) -> String
    shower = show
    res = do
      (DT dt ns) <-
        liftParse (queryToSequent env thrms q) >>= liftSR . runSearch
      newThrms <- tryInsertTheorem nm (q, fromNS ns) thrms
      return (transitions dt, newThrms)

query
  :: forall a cty axlr fr eb axr ctr.
     ( Show a
     , BaseCtrl eb cty a
     , Ord a
     , Ord (eb a)
     , Ord (cty a)
     , ReprAxList axlr
     , ReprFrml fr a
     )
  => (AxEnv axr ctr cty a)
  -> (ThrmEnv axlr fr eb cty a)
  -> (QueriedSeq axlr fr)
  -> UI ()
query env thrms q = flip (toUI' logUI) implsM $ \impls -> do
  logUI ("provable with " ++ (show . length $ impls) ++ " transitions")
  forM_ impls (logUI . shower)
  where
    shower :: (SFormula U U a, SFormula U U a) -> String
    shower = show
    implsM = fmap (transitions . term) $
      liftParse (queryToSequent env thrms q) >>= uiSearch

uiSearch
  :: forall eb cty a.
     (BaseCtrl eb cty a, Ord a, Ord (eb a), Ord (cty a))
  => Sequent eb cty a
  -> ExceptT String (Free UIF) (DT (Terms a) (NeutralSequent eb cty a Labels) Labels)
uiSearch = l . s
  where
    s :: Sequent eb cty a -> SearchRes (DTSequent (Terms a) eb cty a Labels)
    s = runSearch
    l :: SearchRes (DTSequent (Terms a) eb cty a Labels)
      -> ExceptT String (Free UIF) (DT (Terms a) (NeutralSequent eb cty a Labels) Labels)
    l = liftSR

processTheorems
  :: ( ElemBase eb a
     , BaseCtrl eb cty a
     , Ord a
     , Ord (cty a)
     , Ord (eb a)
     , ReprFrml fr a
     , ReprAxList axlf
     )
  => (AxEnv axr ctr cty a)
  -> (ThrmEnv axlf fr eb cty a)
  -> UI (ThrmEnv axlf fr eb cty a)
processTheorems axioms = processThrms doer
  where
    doer (TN name) (q, _) thrms = fmap ((,) q) . toUI Nothing . fmap Just $
      adjoinMsgEUI ("theorem " ++ name ++ " failed: ") (doer' axioms thrms q)
    doer' env thrms q = do
      actualSequent <- liftParse (queryToSequent env thrms q)
      (DT _ ns) <- liftSR (runSearch actualSequent)
      return (fromNS ns)

queryToSequent
  :: forall axlf fr eb cty a axr ctr.
     (Ord (eb a), Ord a, Ord (cty a), ReprAxList axlf, ReprFrml fr a)
  => (AxEnv axr ctr cty a)
  -> (ThrmEnv axlf fr eb cty a)
  -> (QueriedSeq axlf fr)
  -> Either String (Sequent eb cty a)
queryToSequent env thrms (QS axiomsString q1 q2) = do
  lctxt <-
    (fmap (fmap sAtom) .
     adjoinMsgE "linear context: " . reprFrml $
     q1) :: Either String (NE.NonEmpty (SFormula eb cty a))
  concl <-
    fmap (foldr1 sConj . fmap sAtom) $
    adjoinMsgE "conclusion: " . reprFrml $ q2
  axioms <- adjoinMsgE "axioms: " (axsFromList env thrms axiomsString)
  return $ SQ (fromFoldable axioms) (fromFoldable lctxt) concl

changeAxiom
  :: ( ReprAx axr ctr cty a
     , ElemBase eb a
     , BaseCtrl eb cty a
     , Ord a
     , Ord (cty a)
     , Ord (eb a)
     , ReprFrml fr a
     , ReprAxList axlr
     )
  => (AxEnv axr ctr cty a)
  -> ThrmName
  -> ctr
  -> axr
  -> axr
  -> (ThrmEnv axlr fr eb cty a)
  -> UI (AxEnv axr ctr cty a, ThrmEnv axlr fr eb cty a)
changeAxiom axEnv axName axCS axFrom axTo thrms = toUI (axEnv, thrms) $ do
  axiom <- liftParse (reprAx axFrom axCS axTo)
  let newAxEnv = feReplace axName (AAx axFrom axCS axTo, axiom) axEnv
  newThrms <- toEUI (processTheorems newAxEnv thrms)
  return (newAxEnv, newThrms)

removeAxiom
  :: ( ElemBase eb a
     , BaseCtrl eb cty a
     , Ord a
     , Ord (cty a)
     , Ord (eb a)
     , ReprFrml fr a
     , ReprAxList axlf
     )
  => (AxEnv axr ctr cty a)
  -> ThrmName
  -> (ThrmEnv axlf fr eb cty a)
  -> UI (AxEnv axr ctr cty a, ThrmEnv axlf fr eb cty a)
removeAxiom axEnv axName thrms = do
  let newAxioms = feRemove axName axEnv
  newThrms <- processTheorems newAxioms thrms
  return (newAxioms, newThrms)

loadFile
  :: forall ctr axr fr axlr eb cty a.
     ( CParse ctr axr fr axlr
     , ReprAx axr ctr cty a
     , CPrintAx axr ctr
     , CPrintThrm axlr fr
     , ReprFrml fr a
     , ReprAxList axlr
     , ElemBase eb a
     , Show a
     , BaseCtrl eb cty a
     , Ord a
     , Ord (cty a)
     , Ord (eb a)
     )
  => FilePath
  -> StateT (AxEnv axr ctr cty a, ThrmEnv axlr fr eb cty a) (Free UIF) ()
loadFile path = do
  contents <- lift $ uiLoadFile path
  let commandsE = mapM parser (lines contents)
  case commandsE of
    Left err -> lift . logUI $ "error parsing the file: " ++ (show err)
    Right commands -> mapM_ execCommand commands
  where
    parser :: String -> Either String (Command ctr axr fr axlr)
    parser = parseCommand

saveToFile
  :: forall axlr fr axr ctr eb cty a.
     (CPrintAx axr ctr, CPrintThrm axlr fr)
  => (AxEnv axr ctr cty a) -> (ThrmEnv axlr fr eb cty a) -> FilePath -> UI ()
saveToFile axEnv thrms path =
  uiSaveFile path . concat $ aux axStrs ++ aux thrmStrs
  where
    axStrs = printAxAll axEnv
    thrmStrs = printThrmAll thrms
    aux = (++ ["\n"]) . intersperse "\n"

--------------------------------------------------------------------------------
-- Generic command execution

execCommand'
  :: ( ReprAx axr ctr cty a
     , CParse ctr axr fr axlr
     , CPrintAx axr ctr
     , CPrintThrm axlr fr
     , ReprFrml fr a
     , ReprAxList axlr
     , ElemBase eb a
     , Show a
     , BaseCtrl eb cty a
     , Ord a
     , Ord (cty a)
     , Ord (eb a)
     )
  => Command ctr axr fr axlr
  -> AxEnv axr ctr cty a
  -> ThrmEnv axlr fr eb cty a
  -> UI (AxEnv axr ctr cty a, ThrmEnv axlr fr eb cty a)
execCommand' c axEnv thrms = fmap snd $ runStateT (execCommand c) (axEnv, thrms)

execCommand
  :: forall axr ctr cty a eb fr axlr.
     ( ReprAx axr ctr cty a
     , CParse ctr axr fr axlr
     , CPrintAx axr ctr
     , CPrintThrm axlr fr
     , ReprFrml fr a
     , ReprAxList axlr
     , ElemBase eb a
     , Show a
     , BaseCtrl eb cty a
     , Ord a
     , Ord (cty a)
     , Ord (eb a)
     )
  => Command ctr axr fr axlr
  -> StateT (AxEnv axr ctr cty a, ThrmEnv axlr fr eb cty a) (Free UIF) ()
execCommand (AddAxiom name ctrlset strFrom strTo) = do
  (env, thrms) <- get
  newEnv <- lift $ addAxiom env name ctrlset strFrom strTo
  put (newEnv, thrms)
execCommand (ChangeAxiom name ctrlset strFrom strTo) = do
  (env, thrms) <- get
  (newEnv, newThrms) <- lift $ changeAxiom env name ctrlset strFrom strTo thrms
  put (newEnv, newThrms)
execCommand (RemoveAxiom name) = do
  (env, thrms) <- get
  (newEnv, newThrms) <- lift $ removeAxiom env name thrms
  put (newEnv, newThrms)
execCommand (AddTheorem name q) = do
  (env, thrms) <- get
  newThrms <- lift $ addTheorem env thrms name q
  put (env, newThrms)
execCommand (Query q) = do
  (env, thrms) <- get
  lift (query env thrms q)
execCommand (LoadFile path) = loadFile @ctr @axr @fr @axlr @_ @_ @_ path
execCommand (SaveToFile path) = do
  (env, thrms) <- get
  lift $ saveToFile env thrms path

--------------------------------------------------------------------------------
-- Search

newtype LabelMonad a =
  LM {unLM :: (State Int a)}
  deriving (Functor, Applicative, Monad, MonadState Int)

instance PickMonad LabelMonad Int where
  pick = do
    i <- get
    put (i + 1)
    return i

runSearch
  :: ( Ord a
     , ElemBase eb a
     , Ord (eb a)
     , Ord (cty a)
     , BaseCtrl eb cty a
     )
  => Sequent eb cty a -> SearchRes (DTSequent (Terms a) eb cty a Labels)
runSearch actualSequent = mySearch initS initR neutral
  where
    neutral = fst $ runState (unLM . myNeutralize $ actualSequent) 0
    (initS, initR) = initialSequentsAndRules neutral

--isr :: QGSeq -> (S.Set (QDTSeq), [QUnaryRule])
-- isr = initialSequentsAndRules

data SearchRes a = OkRes a | Saturated | ThresholdBreak deriving (Functor)
instance Applicative SearchRes where
  pure = return
  (<*>) = ap
instance Monad SearchRes where
  return = OkRes
  (OkRes x) >>= f = f x
  Saturated >>= _ = Saturated
  ThresholdBreak >>= _ = ThresholdBreak
instance Alternative SearchRes where
  empty = mzero
  (<|>) = mplus
instance MonadPlus SearchRes where
  mzero = Saturated
  mplus (OkRes x) _ = OkRes x
  mplus Saturated x = x
  mplus ThresholdBreak x = x

instance SearchMonad SearchRes where
  failSaturated = Saturated
  failThresholdBreak = ThresholdBreak

-- mySearch :: S.Set QDTSeq -> [QUnaryRule] -> QGSeq -> SearchRes QDTSeq
mySearch
  :: (ElemBase eb a, Ord l, Ord a, Ord (cty a))
  => S.Set (DTSequent (Terms a) eb cty a l)
  -> [UnaryRule (Terms a) eb cty a l]
  -> (GoalNeutralSequent eb cty a l)
  -> SearchRes (DTSequent (Terms a) eb cty a l)
mySearch seqs rules = runIdentity . proverSearch seqs rules

myNeutralize
  :: (Ord a, Ord (eb a), Ord (cty a))
  => Sequent eb cty a -> LabelMonad (GoalNeutralSequent eb cty a Labels)
myNeutralize = flip neutralize Nothing



--------------------------------------------------------------------------------
-- Aux

-- parseCtrlSet :: String -> Either String (SimpleCtrlSet BioAtoms)
-- parseCtrlSet str = fmap ctrlFromFoldable . parseBioAggregate $ str

-- splitTrim :: String -> [String]
-- splitTrim str = filter (not . null) $ map trim $ splitOn "," (trim str)

-- trim :: String -> String
-- trim = dropWhileEnd isSpace . dropWhile isSpace
