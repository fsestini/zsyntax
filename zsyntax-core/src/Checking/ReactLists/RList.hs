{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Checking.ReactLists.RList (RList(..), extendRList, respectsRList) where

import Data.Monoid ((<>))
import Data.Semigroup hiding ((<>))
import Data.Bifunctor (first)
import Checking.ReactLists.Sets
import LFormula
import Rules

{-| A reaction list is a list of pairs, where in each pair the first component
    is an elementary base, and the second component is a control set. -}
newtype RList eb cs = RL
  { unRL :: [(eb, cs)]
  } deriving (Eq, Ord, Semigroup, Monoid)

extendRList :: Monoid eb => eb -> RList eb cs -> RList eb cs
extendRList base = RL . map (first (base <>)) . unRL

respectsRList
  :: (Monoid eb, BaseCtrl eb cs)
  => eb -> RList eb cs -> Bool
respectsRList base (RL rl) = and (map (uncurry respects . first (base <>)) rl)

instance Ord a =>
         HasControlType (SrchFormula eb (RList (ElemBase a) (CtrlSet a)) a l)

instance (Monoid eb, BaseCtrl eb cs) => BaseCtrl eb (RList eb cs) where
  respects = respectsRList
