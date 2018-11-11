{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}

{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Otter.Relation
  ( Rel(..)
  , liftFun
  , liftMaybeToRel
  , relDimap
  , arrowDimap
  ) where

import Data.Bifunctor
-- import TypeClasses
import Control.Monad
import Control.Monad.Fail
import Control.Applicative

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
newtype Rel a b = Rel { unRel :: Maybe (Either b (a -> Rel a b)) }

instance Functor (Rel a) where
  fmap f rel = rel >>= (return . f)

arrowDimap :: (a -> b) -> (c -> d) -> (b -> c) -> (a -> d)
arrowDimap f g h x = g (h (f x))

relDimap :: (a -> b) -> (c -> d) -> Rel b c -> Rel a d
relDimap f g = Rel . fmap (bimap g (arrowDimap f (relDimap f g))) . unRel

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

instance Alternative (Rel a) where
  empty = Rel Nothing
  (Rel Nothing) <|> rel = rel
  rel <|> _ = rel

instance MonadPlus (Rel a) where

instance MonadFail (Rel a) where
  fail _ = Rel Nothing

liftMaybeToRel :: Maybe b -> Rel a b
liftMaybeToRel m = Rel (fmap Left m)

liftFun :: (a -> Maybe b) -> Rel a b
liftFun f = Rel . Just . Right $ liftMaybeToRel . f
