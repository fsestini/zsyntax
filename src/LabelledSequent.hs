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
data LabelledSequent l a  =  LS (UnrestrCtxt l a) (LinearCtxt l a) (Label l a)

instance Eq (LabelledSequent l a) where
  (==) = undefined

instance Ord (LabelledSequent l a) where
  compare = undefined
