{-# LANGUAGE MultiParamTypeClasses #-}

module Prover.Class where

import Control.Monad (forM_)
import Formula
import Rule
import qualified Data.Set as S

class HasProverState l a m where
  getRules :: m ([Rule l a])
  addRule :: Rule l a -> m ()
  addInactive :: LabelledSequent l a -> m ()
  popInactive :: m (Maybe (LabelledSequent l a))
  getActives :: m (S.Set (LabelledSequent l a))
  addActive :: LabelledSequent l a -> m ()
  isNotSubsumed :: LabelledSequent l a -> m Bool
  removeSubsumedBy :: LabelledSequent l a -> m ()

class HasProverEnvironment l a m where
  subsumesGoal :: LabelledSequent l a -> m Bool

addActives
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (LabelledSequent l a) -> m ()
addActives = mapM_ addActive

addInactives
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (LabelledSequent l a) -> m ()
addInactives = mapM_ addInactive

addRules
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (Rule l a) -> m ()
addRules = mapM_ addRule

filterM :: (Monad m) => (a -> m Bool) -> [a] -> m [a]
filterM p [] = return []
filterM p (x : xs) = do
  result <- p x
  rest <- filterM p xs
  if result
     then return $ x : rest
     else return rest

filterUnsubsumed
  :: (HasProverState l a m, Monad m)
  => [LabelledSequent l a] -> m [LabelledSequent l a]
filterUnsubsumed = filterM isNotSubsumed
