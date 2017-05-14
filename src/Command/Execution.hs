{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
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
import Command.Parser
import Command.Export

type MySeq a = Sequent SimpleElemBase SimpleCtrlSet a
type MyNSeq a = NeutralSequent SimpleElemBase SimpleCtrlSet a Labels
type MyDTSeq a = DTSequent (SimpleDerTerm a) SimpleElemBase SimpleCtrlSet a Labels
type MyUnaryRule a = UnaryRule (SimpleDerTerm a) SimpleElemBase SimpleCtrlSet a Labels
type MyGSeq a = GoalNeutralSequent SimpleElemBase SimpleCtrlSet a Labels
type MySF a = SFormula SimpleElemBase SimpleCtrlSet a

--------------------------------------------------------------------------------
-- Querying types

type BioAtoms = String
type Labels = Int

type QSeq = MySeq BioAtoms
type QNSeq = MyNSeq BioAtoms
type QDTSeq = MyDTSeq BioAtoms
type QUnaryRule = MyUnaryRule BioAtoms
type QGSeq = MyGSeq BioAtoms
type QSF = MySF BioAtoms
type QAxiom = SAxiom SimpleCtrlSet BioAtoms

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

tryInsertTheorem :: ThrmName -> (QueriedSeq, Either SA SF) -> ThrmEnv -> EUI ThrmEnv
tryInsertTheorem nm@(TN name) (q, frml) thrms =
  maybe (throwE msg >> return thrms) return newThrms
  where
    newThrms = feInsert nm (q, Just frml) thrms
    msg = "theorem named '" ++ name ++ "' already present"

tryInsertAxiom :: ThrmName -> SA -> AxEnv -> EUI AxEnv
tryInsertAxiom name@(TN nm) axiom env =
  maybe (throwE msg) return (feInsert name axiom env)
  where
    msg = "axiom named '" ++ nm ++ "' already present"

parseAxiom :: String -> String -> CSString
           -> Either String (SAxiom SimpleCtrlSet String)
parseAxiom strFrom strTo (CSS ctrlset) = do
  ctrl <- bimap show id $ parseCtrlSet ctrlset
  fromAggr <- parseBioAggregate1 strFrom
  toAggr <- parseBioAggregate1 strTo
  return $
    sAx (foldr1 bsConj . fmap bsAtom $ fromAggr)
        (foldr1 bsConj . fmap bsAtom $ toAggr)
        ctrl

addAxiom :: AxEnv -> ThrmName -> CSString -> String -> String -> UI AxEnv
addAxiom env name@(TN nm) ctrlset strFrom strTo =
  case (parseAxiom strFrom strTo ctrlset) of
    Left err -> (logUI $ "parse error: " ++ (show err)) >> return env
    Right axiom ->
      case feInsert name axiom env of
        Just newEnv -> return newEnv
        Nothing ->
          logUI ("Axiom named '" ++ nm ++ "' already present") >> return env

-- TODO: Ensure that lc is non-empty
fromNS :: NeutralSequent SimpleElemBase SimpleCtrlSet BioAtoms l -> Either SA SF
fromNS (NS _ lc cs concl@(OLF conclF)) =
  maybe (Right (sImpl lcf mempty cs (fromLFormula conclF))) Left $ do
    from <- decideSF lcf
    to <- decideOLF concl
    return $ sAx from (fmap (const ()) to) cs
  where
    lcf = foldr1 sConj (fmap fromNF (toList lc))
    decideSF :: SFormula eb cs a -> Maybe (BSFormula cs a)
    decideSF (SF olf) = decideOLF olf

addTheorem :: AxEnv -> ThrmEnv -> ThrmName -> QueriedSeq -> Free UIF (ThrmEnv)
addTheorem env thrms nm q =
  flip (toUI' ((>> return thrms) . logUI)) res $ \(impls, newThrms) -> do
    logUI ("provable with " ++ (show . length $ impls) ++ " transitions")
    forM_ impls (logUI . show)
    return newThrms
  where
    res = do
      (DT dt ns) <-
        liftParse (queryToSequent env thrms q) >>= liftSR . runSearch
      newThrms <- tryInsertTheorem nm (q, fromNS ns) thrms
      return (transitions dt, newThrms)

query :: AxEnv -> ThrmEnv -> QueriedSeq -> UI ()
query env thrms q = flip (toUI' logUI) implsM $ \impls -> do
  logUI ("provable with " ++ (show . length $ impls) ++ " transitions")
  forM_ impls (logUI . show)
  where
    implsM = fmap (transitions . term) $
      liftParse (queryToSequent env thrms q) >>= liftSR . runSearch

processTheorems :: AxEnv -> ThrmEnv -> UI ThrmEnv
processTheorems axioms = processThrms doer
  where
    doer (TN name) (q, _) thrms = fmap ((,) q) . toUI Nothing . fmap Just $
      adjoinMsgEUI ("theorem " ++ name ++ " failed: ") (doer' axioms thrms q)
    doer' env thrms q = do
      actualSequent <- liftParse (queryToSequent env thrms q)
      (DT _ ns) <- liftSR (runSearch actualSequent)
      return (fromNS ns)

queryToSequent :: AxEnv -> ThrmEnv -> QueriedSeq -> Either String QSeq
queryToSequent env thrms (QS (AS axiomsString) q1 q2) = do
  lctxt <-
    fmap (fmap sAtom) $ adjoinMsgE "linear context: " (parseBioAggregate1 q1)
  concl <-
    fmap (foldr1 sConj . fmap sAtom) $
    adjoinMsgE "conclusion: " (parseBioAggregate1 q2)
  axioms <- adjoinMsgE "axioms: "
      (mapM (parseAxiomStr env thrms) (splitTrim axiomsString))
  return $
    SQ (fromFoldable axioms) (fromFoldable (lctxt :: NE.NonEmpty QSF)) concl

changeAxiom :: AxEnv -> ThrmName -> CSString -> String -> String -> ThrmEnv
            -> UI (AxEnv, ThrmEnv)
changeAxiom axEnv axName axCS axFrom axTo thrms = toUI (axEnv, thrms) $ do
  axiom <- liftParse (parseAxiom axFrom axTo axCS)
  let newAxEnv = feReplace axName axiom axEnv
  newThrms <- toEUI (processTheorems newAxEnv thrms)
  return (newAxEnv, newThrms)

removeAxiom :: AxEnv -> ThrmName -> ThrmEnv -> UI (AxEnv, ThrmEnv)
removeAxiom axEnv axName thrms = do
  let newAxioms = feRemove axName axEnv
  newThrms <- processTheorems newAxioms thrms
  return (newAxioms, newThrms)

loadFile :: FilePath -> StateT (AxEnv, ThrmEnv) (Free UIF) ()
loadFile path = do
  contents <- lift $ uiLoadFile path
  let commandsE = mapM (parseCommand) (lines contents)
  case commandsE of
    Left err -> lift . logUI $ "error parsing the file: " ++ (show err)
    Right commands -> mapM_ execCommand commands

saveToFile :: AxEnv -> ThrmEnv -> FilePath -> UI ()
saveToFile axEnv thrms path =
  uiSaveFile path . concat $ aux axStrs ++ aux thrmStrs
  where
    axStrs = ppAxEnv axEnv
    thrmStrs = ppThrmEnv thrms
    aux = (++ ["\n"]) . intersperse "\n"

--------------------------------------------------------------------------------
-- Generic command execution

execCommand' :: Command -> AxEnv -> ThrmEnv -> UI (AxEnv, ThrmEnv)
execCommand' c axEnv thrms = fmap snd $ runStateT (execCommand c) (axEnv, thrms)

execCommand
  :: Command -> StateT (AxEnv, ThrmEnv) (Free UIF) ()
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
execCommand (LoadFile path) = loadFile path
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

runSearch :: QSeq -> SearchRes QDTSeq
runSearch actualSequent = mySearch initS initR neutral
  where
    neutral = fst $ runState (unLM . myNeutralize $ actualSequent) 0
    (initS, initR) = isr neutral

isr :: QGSeq -> (S.Set (QDTSeq), [QUnaryRule])
isr = initialSequentsAndRules

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

mySearch :: S.Set QDTSeq -> [QUnaryRule] -> QGSeq -> SearchRes QDTSeq
mySearch seqs rules = runIdentity . proverSearch seqs rules

myNeutralize :: QSeq -> LabelMonad QGSeq
myNeutralize = flip neutralize Nothing

--------------------------------------------------------------------------------
-- Aux

parseCtrlSet :: String -> Either String (SimpleCtrlSet BioAtoms)
parseCtrlSet str = fmap ctrlFromFoldable . parseBioAggregate $ str

parseAxiomStr :: AxEnv -> ThrmEnv -> String -> Either String QAxiom
parseAxiomStr env thrms str =
  case feLookup (TN str) env <|>
       (join . fmap (join . fmap (either Just (const Nothing)) . snd) $
        feLookup (TN str) thrms) of
    Nothing -> Left $ "axiom '" ++ str ++ "' not in scope"
    Just ax -> Right ax

splitTrim :: String -> [String]
splitTrim str = filter (not . null) $ map trim $ splitOn "," (trim str)

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace
