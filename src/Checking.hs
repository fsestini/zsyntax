{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Checking
  ( SimpleCtrlSet
  , SimpleElemBase
  , ctrlFromFoldable
  ) where

import RelFormula (ControlSet(..), ElemBase(..), BaseCtrl(..), BioFormula)
import qualified Data.Set as S
import Data.Foldable (toList)
import qualified TypeClasses as T (CanMap(..))

newtype SimpleCtrlSet a =
  CS (S.Set (BioFormula a))
  deriving (Eq, Ord, Monoid, Show)
newtype SimpleElemBase a =
  EB (S.Set (BioFormula a))
  deriving (Eq, Ord, Monoid, Show)

instance (Eq a, Ord a) => ElemBase SimpleElemBase a where
  singleton = EB . S.singleton

instance Ord a => ControlSet SimpleCtrlSet a where

instance Ord a => BaseCtrl SimpleElemBase SimpleCtrlSet a where
  respects (EB eb) (CS cs) = S.null $ S.intersection eb cs

-- TODO: mega hack
ctrlFromFoldable
  :: (Foldable f, Ord a)
  => f (BioFormula a) -> SimpleCtrlSet a
ctrlFromFoldable f = CS (S.fromList . toList $ f)

instance T.CanMap SimpleCtrlSet where
  type Constr SimpleCtrlSet x = Ord x
  map f (CS s) = CS (S.map (fmap f) s)

instance T.CanMap SimpleElemBase where
  type Constr SimpleElemBase x = Ord x
  map f (EB s) = EB (S.map (fmap f) s)
