{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Frontier (initialSequentsAndRules, DTSequent, UnaryRule) where
  -- ( initialSequentsAndRules
  -- ) where

{-

  Given a goal Gamma ; Delta ===> Q, its frontier contains

  1. All top-level formulas in Gamma^-_! , Delta^-_. , and Q^+_.
  2. For any A in Gamma, Delta, the collection f(A)^-
  3. The collection f(Q)^+

-}

import Data.Foldable
import Data.Monoid
import TypeClasses (filterOut, partitionEithers)
import LabelledSequent
import RelFormula
import qualified Data.Set as S
import Relation
import Rel
import Control.Arrow
import DerivationTerm
-- import SFormula (fromLFormula)
import Context

--------------------------------------------------------------------------------
-- Decorated formulas

-- | Decoration kind.
data FShape = NonAtomic | LBNAtom | RBNAtom | LBPAtom | RBPAtom

-- | Decorated formulas
data DecFormula :: (* -> *) -> (* -> *) -> * -> * -> * where
  Unrestr :: Axiom eb cs a l -> DecFormula eb cs a l
  LinearNegative :: ImplFormula eb cs IRegular a l -> DecFormula eb cs a l
  LinearPositive :: OLFormula eb cs a l -> DecFormula eb cs a l
  deriving (Eq, Ord)

--------------------------------------------------------------------------------
-- Frontier computation

filterImpl :: [NeutralFormula eb cs a l] -> [ImplFormula eb cs IRegular a l]
filterImpl = filterOut . map aux
  where
    aux :: NeutralFormula eb cs a l -> Maybe (ImplFormula eb cs IRegular a l)
    aux (NF (Impl' f)) = Just f
    aux _ = Nothing

-- | Computes the frontier of a labelled sequent.
frontier
  :: forall a l eb cs . (Ord a, Ord l, ElemBase eb a)
  => GoalNeutralSequent eb cs a l -> S.Set (DecFormula eb cs a l)
frontier (GNS uc lc _ (OLF goal)) =
  toplevelUC <> toplevelLC <> S.singleton (LinearPositive (OLF goal)) <>
  ucFrontier <>
  linFrontier <>
  goalFrontier
  where
    toplevelUC = (S.fromList . map Unrestr . asFoldable toList $ uc)
    toplevelLC =
      (S.fromList . map LinearNegative . filterImpl . asFoldable toList $ lc)
    ucFrontier =
      fold . map (frNeg . NF . axiomIsFormula) . asFoldable toList $ uc
    linFrontier = fold . map frNeg . asFoldable toList $ lc
    goalFrontier = frPos goal

frNeg :: (Ord l, Ord a) => NeutralFormula eb cs a l -> S.Set (DecFormula eb cs a l)
frNeg f@(NF (Atom _)) = mempty
frNeg f@(NF (Impl a _ _ b _)) = foc a <> act b

frPos :: (Ord l, Ord a) => LFormula eb cs k a l -> S.Set (DecFormula eb cs a l)
frPos (Atom _) = mempty
frPos f@(Conj _ _ _) = foc f
frPos (Impl a _ _ b _) =
  act a <> frPos b <> S.singleton (LinearPositive (OLF b))

foc :: (Ord l, Ord a) => LFormula eb cs k a l -> S.Set (DecFormula eb cs a l)
foc (Atom _) = mempty
foc (Conj f1 f2 _) = foc f1 <> foc f2
foc f@(Impl _ _ _ _ _) = S.singleton (LinearPositive (OLF f)) <> frPos f

act :: (Ord l, Ord a) => LFormula eb cs k a l -> S.Set (DecFormula eb cs a l)
act a@(Atom _) = mempty
act (Conj a b _) = act a <> act b
act f@(Impl' impl) = S.singleton (LinearNegative impl) <> frNeg (NF f)

--------------------------------------------------------------------------------
-- Generation of initial rules from the frontier.

generateRule
  :: (BaseCtrl eb cs a, Ord l, Ord a, DerTerm term eb cs a l)
  => DecFormula eb cs a l
  -> Rule term  eb cs a l
generateRule f =
  case f of
    Unrestr axiom -> copyRule axiom
    LinearNegative impl -> implLeft impl
    LinearPositive (OLF orf) ->
      case orf of
        Atom _ -> focus orf
        Conj _ _ _ -> focus orf
        Impl' impl -> implRight impl

--------------------------------------------------------------------------------
-- Main function

type UnaryRule term eb cs a l = DTSequent term eb cs a l -> Rule term eb cs a l

initialSequentsAndRules
  :: ( Eq a
     , Eq l
     , Ord l
     , Ord a
     , BaseCtrl eb cs a
     , Ord (cs a)
     , DerTerm term eb cs a l
     , Ord term
     )
  => GoalNeutralSequent eb cs a l
  -> (S.Set (DTSequent term eb cs a l), [UnaryRule term eb cs a l])
initialSequentsAndRules =
  frontier >>>
  S.toList >>>
  map generateRule >>>
  map unRel >>>
  filterOut >>>
  partitionEithers >>>
  (S.fromList *** id)
