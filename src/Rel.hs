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

import TypeClasses
import Control.Monad
import Control.Monad.Fail

{-| A Rel object represents a curried function with an unbounded, unspecified
    number of input arguments, possibly zero.
    Rel elements live in the Maybe monad, so they represent three possible
    situations:

    1. A failing computation which produces nothing;
    2. A successful computation that produces a trivial curried function
       accepting zero arguments (that is, a single value of the return type);
    3. A successful computation that produces a curried function, that is
       a function accepting one argument and returning a new value of type Rel.
 -}
data Rel a b = Rel { unRel :: Maybe (Either b (a -> Rel a b)) }

filterPartitionRel :: (CanPartitionEithers t, Functor t) => t (Rel a b) -> (t b, t (a -> Rel a b))
filterPartitionRel = partitionEithers . filterOut . fmap unRel

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

instance MonadFail (Rel a) where
  fail _ = Rel Nothing
