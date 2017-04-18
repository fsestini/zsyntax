{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Prover.Class
  ( ActiveSequent
  , ActiveSequents
  , activeIsLabelled
  , HasProverEnvironment(..)
  , HasProverState(..)
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

import Control.Monad.Trans.State.Strict hiding (get, put)
import Control.Monad.Trans.Reader hiding (ask)
import Control.Monad.State.Class
import Control.Monad.Reader.Class
import Data.Maybe (listToMaybe)

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

instance (Monad m, Ord l, Ord a) =>
         HasProverState l a (ProverT l a m) where
  getRules = rules <$> get
  addRule r = do
    (PS rls as is gi) <- get
    put (PS (r : rls) as is gi)
  addInactive i = do
    (PS r as is gi) <- get
    put (PS r as (i `S.insert` is) (i `S.insert` gi))
  popInactive = do
    (PS r as is gi) <- get
    put (PS r as (S.fromList . tail . S.toList $ is) gi)
    return . fmap AS . listToMaybe . S.toList $ is
  getActives = do
    (PS _ as _ _) <- get
    return as
  addActive a = do
    (PS r as is gi) <- get
    put (PS r (S.insert a as) is gi)
  isNotSubsumed (AS s) = do
    gi <- S.toList . globalIndex <$> get
    return . not . or . map (\gis -> gis `subsumes` s) $ gi
  removeSubsumedBy (AS s) = do
    (PS r as is gi) <- get
    let newIs = S.filter (\iseq -> not (s `subsumes` iseq)) is
    put (PS r as newIs gi)

instance (Monad m, Ord l, Ord a) =>
         HasProverEnvironment l a (ProverT l a m) where
  getGoal = goalSequent <$> ask
  subsumesGoal s = do
    gs <- convertedGoalSequent <$> ask
    return $ s `subsumes` gs
