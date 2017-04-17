{-# OPTIONS_GHC -Wall #-}

{-| Module of labelled sequents, sequent schemas and related types
    and functions. -}
module LabelledSequent where

import Formula (Label)
import qualified Data.Set as S
import qualified Data.Map.Strict as M

-- | Type of unrestricted contexts.
type UnrestrCtxt l a = S.Set (Label l a)

emptyUnrestrCtxt :: UnrestrCtxt l a
emptyUnrestrCtxt = S.empty

-- | Type of positive natural numbers (hence excluding zero).
data PosNat = One | Succ PosNat deriving (Eq, Show)

-- | Translation from positive naturals to integers.
toInt :: PosNat -> Int
toInt One       =  1
toInt (Succ n)  =  toInt n + 1

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

mergeUnrestrCtxt :: UnrestrCtxt l a -> UnrestrCtxt l a -> UnrestrCtxt l a
mergeUnrestrCtxt = undefined

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
     , label :: (Label l a) }
  deriving (Eq)

subsumedBy
  :: (Eq l, Ord l, Ord a)
  => LabelledSequent l a -> LabelledSequent l a -> Bool
subsumedBy (LS uc1 lc1 l1) (LS uc2 lc2 l2) =
  lc1 == lc2 && l1 == l2 && (uc1 `S.isSubsetOf` uc2)

instance (Eq l, Ord l, Ord a, Eq a) =>
         Ord (LabelledSequent l a) where
  compare s1 s2 =
    if s1 == s2
      then EQ
      else if s1 `subsumedBy` s2
             then LT
             else GT
