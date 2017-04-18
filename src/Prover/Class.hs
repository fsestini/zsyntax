{-# LANGUAGE MultiParamTypeClasses #-}

module Prover.Class where

import Control.Monad (forM_)
import Formula
import LabelledSequent
import Rule
import qualified Data.Set as S

-- | An active sequent is a notable kind of labelled sequent.
newtype ActiveSequent l a = AS (LabelledSequent l a)
type ActiveSequents l a = S.Set (LabelledSequent l a)

-- | Every active sequent is a labelled sequent.
activeIsLabelled :: ActiveSequent l a -> LabelledSequent l a
activeIsLabelled (AS s) = s

class HasProverState l a m where
  getRules :: m ([Rule l a])
  addRule :: Rule l a -> m ()
  addInactive :: LabelledSequent l a -> m ()
  popInactive :: m (Maybe (ActiveSequent l a))
  getActives :: m (ActiveSequents l a)
  addActive :: ActiveSequent l a -> m ()
  isNotSubsumed :: LabelledSequent l a -> m Bool
  removeSubsumedBy :: LabelledSequent l a -> m ()

class HasProverEnvironment l a m where
  getGoal :: m (Sequent l a)
  subsumesGoal :: LabelledSequent l a -> m Bool

haveGoal
  :: (Monad m, HasProverEnvironment l a m)
  => [LabelledSequent l a] -> m (Maybe (LabelledSequent l a))
haveGoal [] = return Nothing
haveGoal (sequent:rest) = do
  res <- subsumesGoal sequent
  case res of
    True -> return . Just $ sequent
    False -> haveGoal rest

addActives
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (ActiveSequent l a) -> m ()
addActives = mapM_ addActive

addInactives
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (LabelledSequent l a) -> m ()
addInactives = mapM_ addInactive

addRules
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (Rule l a) -> m ()
addRules = mapM_ addRule

removeSubsumedByAll
  :: (Monad m, Traversable f, HasProverState l a m)
  => f (LabelledSequent l a) -> m ()
removeSubsumedByAll = mapM_ removeSubsumedBy

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
