{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}

module Rel
  ( Rel
  , liftFun
  , filterPartitionRel
  , liftMaybeToRel
  , unRel
  ) where

import Filterable
import Control.Monad

data Rel a b = Rel { unRel :: Maybe (Either b (a -> Rel a b)) }

filterPartitionRel :: (Filterable t, Functor t) => t (Rel a b) -> (t b, t (a -> Rel a b))
filterPartitionRel = fpartitionEithers . filterOut . fmap unRel

liftMaybeToRel :: Maybe b -> Rel a b
liftMaybeToRel m = Rel (fmap Left m)

liftFun :: (a -> Maybe b) -> Rel a b
liftFun f = Rel . Just . Right $ liftMaybeToRel . f

instance Functor (Rel a) where
  fmap f rel = rel >>= (return . f)

instance Applicative (Rel a) where
  pure = return
  (<*>) = ap

instance Monad (Rel a) where
  return = Rel . Just . Left
  (Rel rel) >>= f =
    case rel of
      Nothing -> Rel Nothing
      Just (Left x) -> f x
      Just (Right g) -> Rel . Just . Right $ \input -> g input >>= f
