{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall #-}

module Checking.Constraints where

import Formula (ElementaryBase)
import Checking.World (SFormula, ElemMap)
import qualified Data.Set as S

data PreElemBase a =
  PEB (ElementaryBase a) (S.Set (SFormula a, SFormula a))

newtype PreCtrlSet a = PCS (S.Set (SFormula a, SFormula a)) deriving (Monoid)

preElemBase :: Foldable f => f (SFormula a) -> PreElemBase a
preElemBase = undefined

elementaryBase :: ElemMap a -> PreElemBase a -> ElementaryBase a
elementaryBase = undefined

data BioConstraint l a :: * where
  Respect :: PreElemBase a -> SFormula a -> SFormula a -> BioConstraint l a
  And :: BioConstraint l a -> BioConstraint l a -> BioConstraint l a
  Or :: BioConstraint l a -> BioConstraint l a -> BioConstraint l a
