{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- {-# LANGUAGE NoImplicitPrelude #-}

module TypeClasses
  ( CanPartitionEithers(..)
  , CanMap(..)
  , CanFilter(..)
  , CanPartition(..)
  , filterOut
  ) where

import qualified Data.Set as S
import qualified Data.Either as E
import Prelude hiding (map)

class CanPartitionEithers f where
  partitionEithers :: f (Either a b) -> (f a, f b)

instance CanPartitionEithers [] where
  partitionEithers = undefined

filterOut
  :: (CanMap f, CanPartitionEithers f)
  => f (Maybe a) -> f a
filterOut coll = snd . partitionEithers $ map mapper coll
  where
    mapper Nothing = Left ()
    mapper (Just x) = Right x

class CanMap f where
  map :: (a -> b) -> f a -> f b

instance Functor f => CanMap f where
  map = fmap

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
