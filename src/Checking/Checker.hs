{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeApplications #-}

module Checking.Checker (check, checkAll) where

import Prelude hiding (fail)
import Control.Monad.State hiding (fail)
import Control.Monad.Trans.Except
import DerivationTerm
import Control.Applicative
import Control.Monad.Fail

import Checking.Constraints
import Checking.World
import Checking.Generation

untilFix :: Eq a => a -> (a -> a) -> a
untilFix x f = limitOf (chain x)
  where
    chain y = y : chain (f y)
    limitOf [] = error "should be an infinite list"
    limitOf (x:y:xs) =
      if x == y
        then x
        else limitOf (y : xs)

check
  :: forall m a l . (Ord a, MonadFail m)
  => World a -> DerTerm l a -> m (World a)
check currentW term = do
  (ext, constrs) <- runCheckerT checker
  let transformer :: World a -> World a =
        foldr (\sch fun -> fromExtension sch . fun) id ext
      newW = untilFix currentW transformer
  if (and $ map (checkSchema newW) constrs)
    then return newW
    else fail "constraint check failed"
  where
    checker =
      (generateConstraints term) :: CheckerT m a ([WorldExtSchema a], [BioConstraintSchema a])

checkAll
  :: forall f m l a.
     (Foldable f, MonadFail m, Alternative m, Ord a)
  => World a -> f (DerTerm l a) -> m (World a)
checkAll w = foldr (\t -> (doCheck t <|>)) empty
  where
    doCheck term = runCheckerT ((check w term) :: CheckerT m a (World a))

--------------------------------------------------------------------------------
-- Checker monad transformer.

newtype CheckerT m a b = C { unC :: StateT ([BioConstraintSchema a], [WorldExtSchema a]) m b }

runCheckerT :: Functor m => CheckerT m a b -> m b
runCheckerT = fmap fst . flip runStateT ([], []) . unC

deriving instance Functor m => Functor (CheckerT m a)
deriving instance Monad m => Applicative (CheckerT m a)
deriving instance Monad m => Monad (CheckerT m a)
deriving instance
         Monad m =>
         MonadState ([BioConstraintSchema a], [WorldExtSchema a])
           (CheckerT m a)
deriving instance MonadFail m => MonadFail (CheckerT m a)

instance Monad m => ConstraintMonad (CheckerT m a) a where
  addBioConstraint c = do
    (bc, wes) <- get
    put (c : bc, wes)
  getBioConstraints = fmap fst get
  addExtSchema s = do
    (bc, wes) <- get
    put (bc, s : wes)
  getExtSchemas = fmap snd get
