{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}

module Command.Execution where

import Text.Parsec.Char
import Text.Parsec hiding (State, token)
import Text.Parsec.String

import qualified Data.List.NonEmpty as NE
import Data.List.Split (splitOn)
import Data.List
import Data.Char

import qualified Data.Map as M
import Context
import TypeClasses (PickMonad(..))
import qualified Data.Set as S
import Relation
import SFormula
import Parser
import Control.Monad.IO.Class
import Control.Arrow ((>>>))
import RelFormula
import Checking
import Text.Parsec (ParseError)
import Data.Bifunctor
import Control.Monad.Trans.State.Strict hiding (get, put)
import Control.Monad.State.Class
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Free
import Control.Monad.Trans
import LinearContext
import RelFormula
import Prover
import Frontier
import Context
import DerivationTerm
import Control.Applicative (Alternative(..))

import Command.Structures
import Command.Parser

type MySeq a = Sequent SimpleElemBase SimpleCtrlSet a
type MyNSeq a = NeutralSequent SimpleElemBase SimpleCtrlSet a Labels
type MyDTSeq a =
  DTSequent (SimpleDerTerm a) SimpleElemBase SimpleCtrlSet a Labels
type MyUnaryRule a =
  UnaryRule (SimpleDerTerm a) SimpleElemBase SimpleCtrlSet a Labels
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
type QAxiom = SAxiom SimpleElemBase SimpleCtrlSet BioAtoms

--------------------------------------------------------------------------------
-- Single command execution

parseAxiom :: String -> String -> CSString
           -> Either String (SAxiom eb SimpleCtrlSet String)
parseAxiom strFrom strTo (CSS ctrlset) = do
  ctrl <- bimap show id $ parseCtrlSet ctrlset
  fromAggr <- parseBioAggregate1 strFrom
  toAggr <- parseBioAggregate1 strTo
  return $
    sAx (foldr1 sConj . fmap sAtom $ fromAggr)
        (foldr1 sConj . fmap sAtom $ toAggr)
        ctrl

addAxiom :: Env -> ThrmName -> CSString -> String -> String -> Free UIF Env
addAxiom env (TN name) ctrlset strFrom strTo =
  case (parseAxiom strFrom strTo ctrlset) of
    Left err -> (logUI $ "parseAxiom error: " ++ (show err)) >> return env
    Right axiom -> return $ M.insert name axiom env

query :: Env -> ThrmEnv -> ThrmName -> QueriedSeq -> Free UIF (ThrmEnv)
query env thrms nm q =
  case (queryToSequent env q) of
    Left err -> (logUI $ "parse error: " ++ err) >> return thrms
    Right actualSequent -> do
      case runSearch actualSequent of
        Saturated -> logUI "Not provable." >> return thrms
        ThresholdBreak ->
          logUI "Search failed: search space too big." >> return thrms
        OkRes (DT dt _ _) ->
          (logUI $ "Provable with " ++ (show (length impls)) ++ " transitions.") >>
          forM_ impls (logUI . show) >>
          return (M.insert nm q thrms)
          where impls = transitions dt

queryToSequent :: Env -> QueriedSeq -> Either String QSeq
queryToSequent env (QS (AS axioms) q1 q2) = do
  lctxt <- fmap (fmap sAtom) $ parseBioAggregate1 q1
  concl <- fmap (foldr1 sConj . fmap sAtom) (parseBioAggregate1 q2)
  axioms <- mapM (parseAxiomStr env) (splitTrim axioms)
  return $
    SQ (fromFoldable axioms) (fromFoldable (lctxt :: NE.NonEmpty QSF)) concl

changeAxiom
  :: Env
  -> ThrmName
  -> CSString
  -> String
  -> String
  -> ThrmEnv
  -> Free UIF (Env, ThrmEnv)
changeAxiom axEnv (TN axName) axCS axFrom axTo thrms =
  case newEnvE of
    Left err -> logUI "error parsing new axiom" >> return (axEnv, thrms)
    Right newEnv ->
      fmap ((,) newEnv) $ foldr (<=<) return (maps newEnv) $ mempty
  where
    mmm env (x, y) = toMap x y (checkThrm env y)
    maps env = map (mmm env) (M.toList thrms)
    newEnvE = do
      ax <- parseAxiom axFrom axTo axCS
      return $ M.insert axName ax axEnv
    checkThrm env =
      queryToSequent env >>>
      pe >>>
      fmap runSearch >>>
      fmap sresToEither >>>
      join >>> (>> return ())
    toMap (TN name) _ (Left err) x =
      (logUI $ "Theorem '" ++ name ++ "' is not provable anymore: " ++ err) >>
      return x
    toMap (TN name) s (Right ()) x =
      (logUI $ "Theorem '" ++ name ++ "' is still provable.") >>
      return (M.insert (TN name) s x)

loadFile :: FilePath -> StateT (Env, ThrmEnv) (Free UIF) ()
loadFile path = do
  contents <- lift $ uiLoadFile path
  let commandsE = mapM (parseCommand) (lines contents)
  case commandsE of
    Left err -> lift . logUI $ "error parsing the file: " ++ (show err)
    Right commands -> mapM_ execCommand commands

--------------------------------------------------------------------------------
-- Generic command execution

execCommand
  :: Command -> StateT (Env, ThrmEnv) (Free UIF) ()
execCommand (AddAxiom name ctrlset strFrom strTo) = do
  (env, thrms) <- get
  newEnv <- lift $ addAxiom env name ctrlset strFrom strTo
  put (newEnv, thrms)
execCommand (ChangeAxiom name ctrlset strFrom strTo) = do
  (env, thrms) <- get
  (newEnv, newThrms) <- lift $ changeAxiom env name ctrlset strFrom strTo thrms
  put (newEnv, newThrms)
execCommand (Query name q) = do
  (env, thrms) <- get
  newThrms <- lift $ query env thrms name q
  put (env, newThrms)
execCommand (LoadFile path) = loadFile path
execCommand (SaveToFile _) = lift $ logUI "saving to files not yet supported"

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

type SrchBioAtoms = Int
type SrchLabels = Int

type SrchSeq = MySeq SrchBioAtoms
type SrchNSeq = MyNSeq SrchBioAtoms
type SrchDTSeq = MyDTSeq SrchBioAtoms
type SrchUnaryRule = MyUnaryRule SrchBioAtoms
type SrchGSeq = MyGSeq SrchBioAtoms
type SrchSF = MySF SrchBioAtoms
type SrchAxiom = SAxiom SimpleElemBase SimpleCtrlSet SrchBioAtoms

toSearchSequent :: QGSeq -> SrchGSeq
toSearchSequent = (gnsMapAtoms hack)
  where
    hack "a" = 1
    hack "b" = 2
    hack "c" = 3
    hack "d" = 4
    hack "e" = 5
    hack _ = error "no hack"

runSearch :: QSeq -> SearchRes SrchDTSeq
runSearch actualSequent = mySearch initS initR neutral
  where
    neutral = fst $ runState (unLM . fmap toSearchSequent . myNeutralize $ actualSequent) 0
    (initS, initR) = isr neutral

isr :: SrchGSeq -> (S.Set (SrchDTSeq), [SrchUnaryRule])
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

mySearch :: S.Set SrchDTSeq -> [SrchUnaryRule] -> SrchGSeq -> SearchRes SrchDTSeq
mySearch seqs rules = runIdentity . proverSearch seqs rules

myNeutralize :: QSeq -> LabelMonad QGSeq
myNeutralize = flip neutralize Nothing

--------------------------------------------------------------------------------
-- Aux

parseCtrlSet :: String -> Either String (SimpleCtrlSet BioAtoms)
parseCtrlSet str = fmap ctrlFromFoldable . parseBioAggregate $ str

parseAxiomStr :: Env -> String -> Either String QAxiom
parseAxiomStr env str =
  case M.lookup str env of
    Nothing -> Left $ "axiom '" ++ str ++ "' not in scope"
    Just ax -> Right ax

trim = dropWhileEnd isSpace . dropWhile isSpace

splitTrim :: String -> [String]
splitTrim str = filter (not . null) $ map trim $ splitOn "," (trim str)

pe :: Either String a -> Either String a
pe = first ("parse error: " ++)

applyTwo :: (a -> b) -> (a -> c) -> a -> (b, c)
applyTwo f g x = (f x, g x)

sresToEither :: SearchRes b -> Either String b
sresToEither (OkRes x) = Right x
sresToEither Saturated = Left ""
sresToEither ThresholdBreak = Left "search diverged"
