{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}

{-| Module of labelled sequents, sequent schemas and related types
    and functions. -}
module LabelledSequent where

import Data.List
import qualified Data.List.NonEmpty as NE
import Formula
       (Label, Sequent(..), OLSLFormula(..), label, olfLabel, olsfLabel)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Semigroup

--------------------------------------------------------------------------------
-- Unrestricted contexts

-- | Type of unrestricted contexts.
newtype UnrestrCtxt l a = UC (S.Set (Label l a)) deriving (Eq, Monoid)

-- | Unrestricted contexts are ordered by set-theoretic inclusion.
instance (Eq l, Ord a, Ord l) => Ord (UnrestrCtxt l a) where
  (UC set1) <= (UC set2) = set1 `S.isSubsetOf` set2

--------------------------------------------------------------------------------
-- Numeric datatypes

data Nat = Zero | NatSucc Nat

-- | Type of positive natural numbers (hence excluding zero).
data PosNat = One | Succ PosNat deriving (Eq, Show)

instance Semigroup PosNat where
  One <> m = Succ m
  Succ n <> m = Succ (n <> m)

neLength :: NE.NonEmpty a -> PosNat
neLength = sconcat . fmap (const One)

--------------------------------------------------------------------------------
-- Linear contexts

{-| Type of linear contexts.

    A linear context is a map from labels to the number of occurrences of that
    label in the context. Such map has positive natural numbers as codomain, to
    enforce the fact that we consider only labels that occur at least once. -}
newtype LinearCtxt l a = LC (M.Map (Label l a) PosNat) deriving (Eq)

instance (Ord a, Ord l) => Monoid (LinearCtxt l a) where
  mempty = LC M.empty
  (LC map1) `mappend` (LC map2) = LC $ M.unionWith (<>) map1 map2

addToLinCtxt
  :: (Ord a, Ord l)
  => (Label l a) -> LinearCtxt l a -> LinearCtxt l a
addToLinCtxt lbl (LC lc) = LC (M.insertWith (<>) lbl One lc)

addToUnrestrCtxt :: (Label l a) -> UnrestrCtxt l a -> UnrestrCtxt l a
addToUnrestrCtxt = undefined

singletonLinearCtxt :: Label l a -> LinearCtxt l a
singletonLinearCtxt = undefined

--------------------------------------------------------------------------------
-- Labelled sequents

{-| Type of labelled sequents.

    A labelled sequent is composed of an unrestricted context, a linear context
    and a goal label.

    Contrary to a labelled formula, a labelled sequent contains labels only, and
    does not retain any information about actual formulas. -}
data LabelledSequent l a =
  LS { unrestrCtxt :: (UnrestrCtxt l a)
     , linearCtxt :: (LinearCtxt l a)
     , goalLabel :: (Label l a) }
  deriving (Eq)

subsumes
  :: (Eq l, Ord l, Ord a)
  => LabelledSequent l a -> LabelledSequent l a -> Bool
subsumes (LS uc1 lc1 l1) (LS uc2 lc2 l2) =
  lc1 == lc2 && l1 == l2 && (uc1 <= uc2)

{-| Ordering is defined in terms of subsumption. This works under the tacit
    assumption that subsumption is a partial ordering, and that (==) is
    equivalent to testing for mutual subsumption. -}
instance (Eq l, Ord l, Ord a) => Ord (LabelledSequent l a) where
  (<=) = subsumes

--------------------------------------------------------------------------------
-- Conversion from fully-specified sequents to labelled sequents.

toLabelledSequent
  :: (Ord a, Ord l, Eq l, Eq a)
  => Sequent l a -> LabelledSequent l a
toLabelledSequent (SQ uc lc goal) =
  LS (UC (S.map olfLabel uc)) (toLabelledLinearCtxt lc) (label goal)

toLabelledLinearCtxt
  :: (Eq a, Eq l, Ord a, Ord l)
  => [OLSLFormula l a] -> LinearCtxt l a
toLabelledLinearCtxt lc = LC (M.fromList occurrences)
  where
    labels = NE.groupBy (==) . sortBy compare . map olsfLabel $ lc
    occurrences = map (\xs -> (NE.head xs, neLength xs)) labels
