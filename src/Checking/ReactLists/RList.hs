{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Checking.ReactLists.RList (RList(..), extendRList, respectsRList) where

import Data.Monoid ((<>))
import Data.Bifunctor (first)
import qualified RelFormula as L (ElemBase, BaseCtrl(..), ControlSet)
import Checking.ReactLists.Sets

{-| A reaction list is a list of pairs, where in each pair the first component
    is an elementary base, and the second component is a control set. -}
newtype RList eb cs a = RL { unRL :: [(eb a, cs a)]} deriving (Eq, Ord, Monoid)

extendRList :: L.ElemBase eb a => eb a -> RList eb cs a -> RList eb cs a
extendRList base = RL . map (first (base <>)) . unRL

respectsRList
  :: L.BaseCtrl eb cs a
  => eb a -> RList eb cs a -> Bool
respectsRList base (RL rl) = and (map (uncurry L.respects . first (base <>)) rl)

instance Eq a => L.ControlSet (RList ElemBase CtrlSet) a where

instance (Eq a, Ord a) => L.BaseCtrl ElemBase (RList ElemBase CtrlSet) a where
  respects = respectsRList
