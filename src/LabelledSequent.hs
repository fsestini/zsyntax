{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}

{-| Module of labelled sequents, sequent schemas and related types
    and functions. -}
module LabelledSequent where

import Data.List
import Formula (Label, NeutralSequent(..), olfLabel, olsfLabel, label)
import qualified Data.Set as S
import Prelude hiding (fail)

import Context (fromFoldable)
import UnrestrContext
import LinearContext

--------------------------------------------------------------------------------
-- Labelled sequents

type LUnrestrCtxt l a = UnrestrCtxt (Label l a)
type LLinearCtxt l a = LinearCtxt (Label l a)

{-| Type of labelled sequents.

    A labelled sequent is composed of an unrestricted context, a linear context
    and a goal label.

    Contrary to a labelled formula, a labelled sequent contains labels only, and
    does not retain any information about actual formulas. -}
data LabelledSequent l a =
  LS { unrestrCtxt :: (LUnrestrCtxt l a)
     , linearCtxt :: (LLinearCtxt l a)
     , goalLabel :: (Label l a) }
  deriving (Eq, Ord)

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
  => NeutralSequent l a -> LabelledSequent l a
toLabelledSequent (NSQ uc lc goal) =
  LS
    (fromFoldable (S.map olfLabel uc))
    (fromFoldable (map olsfLabel lc))
    (label goal)
