{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}

module Zsyntax.CLI.Structures where

import Data.Function (on)
import Data.Composition ((.:))
import Data.Maybe (catMaybes)
import Control.Monad (void)
import Control.Monad.State
-- import Control.Monad.Free (Free, liftF)
import Data.Map (Map)
import qualified Data.Map as M (toList, insert, empty)
import Data.Foldable (toList, foldlM)
import Data.List (uncons) -- , intersperse)
import Data.Bifunctor (second)
import Data.Bitraversable (bitraverse)
-- import Core.FormulaKind (GoalNSequent'(..))
import Data.List.NonEmpty (NonEmpty(..))
-- import Rule.IntFormula (NSequent, NSequent'(..), GoalNSequent, oFormulaBase, lcBase)
import Data.Set (fromList)
import Data.MultiSet (intersection)
import qualified Data.MultiSet as MS (fromList)
import Lens.Micro.Platform (Lens', use, (.=), makeLenses)
import Control.Monad.Except

-- import Data.MultiSet.NonEmpty (fromNEList, toMultiSet)

import Zsyntax.ReactionList
import Zsyntax.Formula ( Sequent(..), Axiom, BioFormula, axiom, atom, conj
                       , axiom', ppBioFormula)
import Zsyntax.Labelled.Formula (withOpaque, elemBase, bConj, unEB,maybeBFormula)
-- , decideN, decideOF, bConj, unEB, bAtom)
import Zsyntax.Labelled.Rule (LSequent(..), GoalNSequent(..), lcBase,withNeutral)

-- import Lens.Micro.Platform (makeLenses)
import Control.Monad.Extra

--------------------------------------------------------------------------------
-- Formulas

type BioAtom = String
type Atom = BioFormula BioAtom

-- type ControlType = Cty -- RList (ElemBase BioAtoms) (CtrlSet (BioFormula BioAtoms))
-- type Axiom = SAxiom ControlType Atom
type Aggregate = NonEmpty Atom -- (BioFormula BioAtoms)
-- type NeutralSequent = LSequent Atom Int
-- type GoalSequent = GoalNSequent _ _ _
-- type Sequent = F.Sequent ControlType Atom
type LabelTy = Int

ppAtom :: Atom -> String
ppAtom = ppBioFormula id

--------------------------------------------------------------------------------
-- Names

type Name = String

--------------------------------------------------------------------------------
-- Query data

data RequiredAxs = Some [Name] | AllOfEm deriving (Eq, Ord, Show)
data AxMode = Normal | Refine deriving (Eq, Ord, Show)

data QueryAxioms = QA
  { _requiredAxs :: RequiredAxs
  , _axMode :: AxMode
  } deriving (Eq, Ord, Show)
data AxRepr = AR
  { _arFrom :: Aggregate
  , _arCtrl :: CtrlSet (BioFormula BioAtom)
  , _arTo :: Aggregate
  } deriving (Eq, Ord)
data QueriedSeq = QS
  { _qsAxioms :: QueryAxioms
  , _qsFrom :: [Atom]
  , _qsTo :: NonEmpty Atom -- Aggregate
  } deriving (Eq, Ord, Show)

mconcatMapM makeLenses [''QueryAxioms, ''AxRepr, ''QueriedSeq]

--------------------------------------------------------------------------------

toAxNames :: (MonadState s m, HasAxEnv s, HasThrmEnv s) => [Axiom Atom] -> m [Name]
toAxNames axs = fmap fst . filter (flip elem axs . snd) <$> legitAxioms

--------------------------------------------------------------------------------

fromNS :: LSequent Atom LabelTy -> Maybe (Axiom Atom)
fromNS (LS _ lc cty cc) = do
  (nel, nelc) <- traverse (withNeutral maybeBFormula) (toList lc) >>= uncons . fmap void
  toFrml <- withOpaque maybeBFormula cc
  pure (axiom' (foldl (bConj ()) nel nelc) cty (void toFrml))

goalDiff :: LSequent Atom LabelTy -> GoalNSequent Atom LabelTy -> Int
goalDiff s g =
  let eb1 = withOpaque elemBase (lsConcl s)
      eb2 = withOpaque elemBase (_gnsConcl g)
      leb1 = lcBase (lsLCtxt s)
      leb2 = lcBase (_gnsLC g)
      f = (length . toList .: intersection) `on` unEB
  in f eb1 eb2 + f leb1 leb2

--------------------------------------------------------------------------------

data ThrmValidity = Valid | NotValid

type AxEnv = Map Name AxRepr
type ThrmEnv = Map Name (QueriedSeq, Maybe (Axiom Atom))

class HasAxEnv s where
  _AxEnv :: Lens' s AxEnv

class HasThrmEnv s where
  _ThrmEnv :: Lens' s ThrmEnv

type MonadZState s m = (MonadState s m, HasAxEnv s, HasThrmEnv s)

queryToGoal :: (MonadError Error m, MonadZState s m) => QueriedSeq -> m (Sequent Atom)
queryToGoal (QS axlist q1 q2) = do
  axioms <- case _requiredAxs axlist of
    Some list -> mapM lookupAxiom list
    AllOfEm -> fmap snd <$> legitAxioms
  let lc = fmap atom q1
      cc = foldr1 conj . fmap atom $ q2
  pure (SQ (fromList axioms) (MS.fromList lc) cc)

legitAxioms :: MonadZState s m => m [(Name, Axiom Atom)]
legitAxioms = (++) <$> fromAxs <*> fromThrms
  where
    reprToAxiom (AR from ctrl to) = axiom from (justCS ctrl) to
    fromAxs = fmap (second reprToAxiom) . M.toList <$> use _AxEnv
    fromThrms = catMaybes . fmap (bitraverse pure id . second snd) . M.toList
                <$> use _ThrmEnv

lookupAxiom :: (MonadError Error m, MonadZState s m) => Name -> m (Axiom Atom)
lookupAxiom nm = do
  m <- lookup nm <$> legitAxioms
  maybe (throwError (AxNotInScope nm)) pure m

processThrms'
  :: Monad m
  => (ThrmEnv -> Name -> (QueriedSeq, Maybe (Axiom Atom))
    -> m (QueriedSeq, Maybe (Axiom Atom)))
  -> ThrmEnv
  -> m ThrmEnv
processThrms' f =
  foldlM (\m p -> fmap (flip (M.insert (fst p)) m) (uncurry (f m) p))
    M.empty . M.toList

processThrms :: (MonadState s m, HasThrmEnv s)
             => (ThrmEnv -> Name -> (QueriedSeq, Maybe (Axiom Atom))
                   -> m (QueriedSeq, Maybe (Axiom Atom)))
             -> m ()
processThrms f = do
  env <- use _ThrmEnv
  env' <- processThrms' f env
  _ThrmEnv .= env'

data Error = AxNameClash Name | ThrmNameClash Name | AxNotInScope Name
  deriving Show
