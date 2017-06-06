{-# LANGUAGE PolyKinds #-}
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
  , CanMap'(..)
  , CMap
  , CanFilter(..)
  , CanPartition(..)
  , PickMonad(..)
  , Coercible(..)
  , Pretty(..)
  , PrettyK(..)
  , filterOut
  , prettys
  , LogMonad(..)
  , mlogPretty
  , mlogShow
  , mlogLn
  ) where

import qualified Data.Set as S
import qualified Data.Either as E
import qualified Data.Either as ET (partitionEithers)
import Prelude hiding (map)
import Data.Foldable
import Data.Constraint
import Data.List (intersperse)

class Monad m => LogMonad m where
  mlog :: String -> m ()

mlogPretty :: (Pretty a, LogMonad m) => a -> m ()
mlogPretty = mlog . pretty

mlogLn :: LogMonad m => String -> m ()
mlogLn str = mlog str >> mlog "\n"

mlogShow :: (Show a, LogMonad m) => a -> m ()
mlogShow = mlog . show

class Pretty a where
  pretty :: a -> String

class PrettyK (f :: k -> *) where
  prettyk :: f a -> String

prettys :: (Pretty a, Foldable f) => f a -> String
prettys = concat . intersperse "," . fmap pretty . toList

instance Pretty String where
  pretty s = s

class CanPartitionEithers f where
  partitionEithers :: f (Either a b) -> (f a, f b)

instance CanPartitionEithers [] where
  partitionEithers = ET.partitionEithers

filterOut :: Foldable f => f (Maybe a) -> [a]
filterOut = snd . E.partitionEithers . fmap mapper . toList
  where
    mapper (Nothing) = Left ()
    mapper (Just x) = Right x

type CMap f a b = (CanMap f, Constr f a, Constr f b)

class CanMap f where
  type Constr f x :: Constraint
  map :: (Constr f a, Constr f b) => (a -> b) -> f a -> f b

class CanMap' f a b where
  map' :: (a -> b) -> f -> f

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
