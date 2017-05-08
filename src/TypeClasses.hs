{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}

module TypeClasses
  ( CanPartitionEithers(..)
  , CanMap(..)
  , CanFilter(..)
  , CanPartition(..)
  , PickMonad(..)
  , Coercible(..)
  , filterOut
  ) where

import qualified Data.Set as S
import qualified Data.Either as E
import qualified Data.Either as ET (partitionEithers)
import Prelude hiding (map)
import Data.Foldable
import Data.Constraint

class CanPartitionEithers f where
  partitionEithers :: f (Either a b) -> (f a, f b)

instance CanPartitionEithers [] where
  partitionEithers = ET.partitionEithers

filterOut :: Foldable f => f (Maybe a) -> [a]
filterOut = snd . E.partitionEithers . fmap mapper . toList
  where
    mapper (Nothing) = Left ()
    mapper (Just x) = Right x

class CanMap f where
  type Constr f x :: Constraint
  map :: (Constr f a, Constr f b) => (a -> b) -> f a -> f b

class CanFilter f where
  filter :: (a -> Bool) -> f a -> f a

class CanPartition f where
  partition :: (a -> Bool) -> f a -> (f a, f a)

class CanSingleton f where
  singleton :: a -> f a

class Denumerable t where
  next :: t -> t

pickFresh :: (Ord t, Foldable f, Denumerable t) => f t -> t
pickFresh = next . maximum

class Monad m => PickMonad m l where
  pick :: m l

class Coercible a b where
  coerce :: a -> b
