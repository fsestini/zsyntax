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

--------------------------------------------------------------------------------
-- Unrestricted contexts

-- | Type of unrestricted contexts.
newtype UnrestrCtxt l a = UC (S.Set (Label l a)) deriving (Eq, Monoid)

--------------------------------------------------------------------------------
-- Numeric datatypes

data Nat = Zero | NatSucc Nat

-- | Type of positive natural numbers (hence excluding zero).
data PosNat = One | Succ PosNat deriving (Eq, Show)

-- | Translation from positive naturals to integers.
toInt :: PosNat -> Int
toInt One       =  1
toInt (Succ n)  =  toInt n + 1

lLength :: [a] -> Nat
lLength [] = Zero
lLength (_ : xs) = NatSucc (lLength xs)

succOfNat :: Nat -> PosNat
succOfNat Zero = One
succOfNat (NatSucc n) = Succ (succOfNat n)

neLength :: NE.NonEmpty a -> PosNat
neLength (_ NE.:| xs) = succOfNat (lLength xs)

--------------------------------------------------------------------------------

{-| Type of linear contexts.

    A linear context is a map from labels to the number of occurrences of that
    label in the context. Such map has positive natural numbers as codomain, to
    enforce the fact that we consider only labels that occur at least once. -}
type LinearCtxt l a = M.Map (Label l a) PosNat

emptyLinearCtxt :: LinearCtxt l a
emptyLinearCtxt = M.empty

addToLinCtxt :: (Label l a) -> LinearCtxt l a -> LinearCtxt l a
addToLinCtxt = undefined

addToUnrestrCtxt :: (Label l a) -> UnrestrCtxt l a -> UnrestrCtxt l a
addToUnrestrCtxt = undefined

mergeLinearCtxt :: LinearCtxt l a -> LinearCtxt l a -> LinearCtxt l a
mergeLinearCtxt = undefined

singletonLinearCtxt :: Label l a -> LinearCtxt l a
singletonLinearCtxt = undefined

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
subsumes (LS (UC uc1) lc1 l1) (LS (UC uc2) lc2 l2) =
  lc1 == lc2 && l1 == l2 && (uc1 `S.isSubsetOf` uc2)

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
toLabelledLinearCtxt lc = M.fromList occurrences
  where
    labels = NE.groupBy (==) . sortBy compare . map olsfLabel $ lc
    occurrences = map (\xs -> (NE.head xs, neLength xs)) labels
