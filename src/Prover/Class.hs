{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Prover.Class
  ( ActiveSequent
  , activeIsLabelled
  , HasProverEnvironment
  , HasProverState
  , haveGoal
  , addActives
  , addInactives
  , addRules
  , removeSubsumedByAll
  , filterM
  , filterUnsubsumed
  , ProverT
  ) where

import Control.Monad (forM_)
import Formula
import LabelledSequent
import Rule
import qualified Data.Set as S

-- | An active sequent is a notable kind of labelled sequent.
newtype ActiveSequent l a = AS (LabelledSequent l a) deriving (Eq, Ord)
type ActiveSequents l a = S.Set (ActiveSequent l a)

-- | Every active sequent is a labelled sequent.
activeIsLabelled :: ActiveSequent l a -> LabelledSequent l a
activeIsLabelled (AS s) = s

-- The prover state must include a global index of all sequents that have been
-- added to the inactive set.
class HasProverState l a m where
  getRules :: m ([Rule l a])
  addRule :: Rule l a -> m ()
  addInactive :: LabelledSequent l a -> m ()
  popInactive :: m (Maybe (ActiveSequent l a))
  getActives :: m (ActiveSequents l a)
  addActive :: ActiveSequent l a -> m ()
  isNotSubsumed :: ActiveSequent l a -> m Bool
  removeSubsumedBy :: ActiveSequent l a -> m ()

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

--------------------------------------------------------------------------------
-- ProverT monad transformer

type InactiveSequents l a = S.Set (LabelledSequent l a)

data ProverState l a = PS
  { rules :: [Rule l a]
  , actives :: ActiveSequents l a
  , inactives :: InactiveSequents l a
  , globalIndex :: InactiveSequents l a
  }
data ProverEnvironment l a = PE
  { goalSequent :: Sequent l a
  , convertedGoalSequent :: LabelledSequent l a
  }

newtype ProverT l a m b = ProverT
  { unProverT :: ReaderT (ProverEnvironment l a) (StateT (ProverState l a) m) b
  }

deriving instance (Functor m) => Functor (ProverT l a m)
deriving instance (Monad m, Applicative m) => Applicative (ProverT l a m)
deriving instance (Monad m) => Monad (ProverT l a m)
deriving instance (Monad m) => MonadState (ProverState l a) (ProverT l a m)
deriving instance (Monad m) => MonadReader (ProverEnvironment l a) (ProverT l a m)
