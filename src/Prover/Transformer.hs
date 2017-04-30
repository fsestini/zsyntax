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

import ForwardSequent

import Prover.Class
import Prover.Structures

--------------------------------------------------------------------------------
-- ProverT monad transformer

data ProverState seqty = PS
  { rules :: [Rule seqty]
  , actives :: ActiveSequents seqty
  , inactives :: InactiveSequents seqty
  , globalIndex :: GlobalIndex seqty
  }

-- data ProverEnvironment l a = PE
--   { goalSequent :: NeutralSequent l a
--   , convertedGoalSequent :: SearchSequent Goal l a
--   }

data ProverEnvironment s = PE
  { -- goalSequent :: NeutralSequent l a
  -- ,
    convertedGoalSequent :: SearchSequent Goal s
  }


newtype ProverT seqty m b = ProverT
  { unProverT :: ReaderT (ProverEnvironment seqty) (StateT (ProverState seqty) m) b
  }

-- runProverT :: ProverT seqty m b -> NeutralSequent seqty -> m b
-- runProverT prover sequent = undefined

deriving instance (Functor m) => Functor (ProverT seqty m)
deriving instance (Monad m) => Applicative (ProverT seqty m)
deriving instance (Monad m) => Monad (ProverT seqty m)
deriving instance (Monad m) => MonadState (ProverState seqty) (ProverT seqty m)
deriving instance (Monad m) => MonadReader (ProverEnvironment seqty) (ProverT seqty m)

instance (Monad m, Ord seqty, ForwardSequent seqty) =>
         HasProverState seqty (ProverT seqty m) where
  getRules = rules <$> get
  addRule r = do
    (PS rls as is gi) <- get
    put (PS (r : rls) as is gi)
  addInactive i = do
    (PS r as is gi) <- get
    put (PS r as (addToInactives is i) (addToIndex gi i))
  popInactive = do
    (PS r as is gi) <- get
    case popInactiveOp is of
      Just (newIs, inactive) -> do
        let (newAs, active) = activate as inactive
        put (PS r newAs newIs gi)
        return . Just $ active
      Nothing -> return Nothing
  getActives = do
    (PS _ as _ _) <- get
    return as
  isNotFwdSubsumed conclSeq = do
    gi <- globalIndex <$> get
    return $ fwdSubsumes gi conclSeq
  removeSubsumedBy fschecked = do
    (PS r as is gi) <- get
    let (newIs, bschecked) = removeSubsumedByOp fschecked is
    put (PS r as newIs gi)
    return bschecked

instance (Monad m, ForwardSequent seqty) =>
         HasProverEnvironment seqty (ProverT seqty m) where
  -- getGoal = goalSequent <$> ask
  subsumesGoal s = do
    gs <- convertedGoalSequent <$> ask
    return (s `Prover.Structures.subsumesGoalOp` gs)
