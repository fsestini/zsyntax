{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Prover.Transformer where

import Data.Maybe (listToMaybe)
import Control.Monad.State.Class
import Control.Monad.Reader.Class
import Control.Monad.Trans
import qualified Data.Map as M
import qualified Data.Set as S
import LabelledSequent
import Formula
import Rule
import Control.Monad.Trans.State.Strict hiding (get, put)
import Control.Monad.Trans.Reader hiding (ask)
import Filterable

import Prover.Class
import Prover.Structures
import Prover.Operations

--------------------------------------------------------------------------------
-- ProverT monad transformer

data ProverState l a = PS
  { rules :: [Rule l a]
  , actives :: ActiveSequents l a
  , inactives :: InactiveSequents l a
  , globalIndex :: S.Set (SearchSequent GlIndex l a)
  }
data ProverEnvironment l a = PE
  { goalSequent :: Sequent l a
  , convertedGoalSequent :: SearchSequent Goal l a
  }

newtype ProverT l a m b = ProverT
  { unProverT :: ReaderT (ProverEnvironment l a) (StateT (ProverState l a) m) b
  }

runProverT :: ProverT l a m b -> Sequent l a -> m b
runProverT prover sequent = undefined

deriving instance (Functor m) => Functor (ProverT l a m)
deriving instance (Monad m) => Applicative (ProverT l a m)
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
    put (PS r as (addToInactives is i) (addToIndex gi i))
  popInactive = do
    (PS r as is gi) <- get
    let newIs = S.fromList . tail . S.toList $ is
        popped = listToMaybe . S.toList $ is
    case popped of
      Just sequent -> do
        let (newActives, active) = activate as sequent
        put (PS r newActives newIs gi)
        return . Just $ active
      Nothing -> return Nothing
  getActives = do
    (PS _ as _ _) <- get
    return as
  isNotFwdSubsumed conclSeq = do
    gi <- S.toList . globalIndex <$> get
    let res = map (flip fwdSubsumes conclSeq) $ gi
        res2 = filterOut res
    if (length res) == (length res2)
       then return . Just . head $ res2 -- !!!! TODO !!!! use non-empty lists!!
       else return Nothing
  removeSubsumedBy fschecked = do
    (PS r as is gi) <- get
    let newIs = S.filter (\iseq -> not (fschecked `bwdSubsumes` iseq)) is
    put (PS r as newIs gi)

instance (Monad m, Ord l, Ord a) =>
         HasProverEnvironment l a (ProverT l a m) where
  getGoal = goalSequent <$> ask
  subsumesGoal s = do
    gs <- convertedGoalSequent <$> ask
    return $ s `Prover.Operations.subsumesGoal` gs
