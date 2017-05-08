{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Prover.Transformer (proverSearch) where

import Data.Maybe (listToMaybe)
import Control.Monad.State.Class
import Control.Monad.Reader.Class
import Control.Monad.Trans
import Control.Monad.Fail
import Control.Applicative
import qualified Data.Map as M
import qualified Data.Set as S
import LabelledSequent
import Formula
import Rule
import Control.Monad.Trans.State.Lazy hiding (get, put)
import Control.Monad.Trans.Reader hiding (ask)
import Data.Foldable

import ForwardSequent
import TypeClasses

import Prover.Class
import Prover.Structures
import Prover.Search

--------------------------------------------------------------------------------

proverSearch'
  :: _
  => f seqty -> [Rule seqty] -> ProverT seqty goalty m (mf seqty)
proverSearch' seqs rules =
  doSearch (S.fromList . fmap initialize . toList $ seqs) rules

proverSearch seqs rules = runProverT (proverSearch' seqs rules)

--------------------------------------------------------------------------------
-- ProverT monad transformer

data ProverState seqty = PS
  { rules :: [Rule seqty]
  , actives :: ActiveSequents seqty
  , inactives :: InactiveSequents seqty
  , globalIndex :: GlobalIndex seqty
  }

data ProverEnvironment s = PE
  { goalSequent :: SearchSequent Goal s
  }

newtype ProverT seqty goalty m b = ProverT
  { unProverT :: ReaderT (ProverEnvironment goalty) (StateT (ProverState seqty) m) b
  }

runProverT
  :: (Functor m, Ord seqty)
  => ProverT seqty goalty m b -> goalty -> m b
runProverT prover sequent =
  fmap fst $ runStateT
               (runReaderT (unProverT prover) (PE (makeGoal sequent)))
               (PS [] emptyActives emptyInactives emptyGlobalIndex)

deriving instance (Functor m) => Functor (ProverT seqty goalty m)
deriving instance (Monad m) => Applicative (ProverT seqty goalty m)
deriving instance (Monad m) => Monad (ProverT seqty goalty m)
deriving instance (Monad m) => MonadState (ProverState seqty) (ProverT seqty goalty m)
deriving instance (Monad m) => MonadReader (ProverEnvironment goalty) (ProverT seqty goalty m)

instance (Monad m, Ord seqty, ForwardSequent seqty) =>
         HasProverState seqty (ProverT seqty goalty m) where
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

instance (Monad m, ForwardSequent goalty, SearchPair seqty goalty) =>
         HasProverEnvironment seqty (ProverT seqty goalty m) where
  isSubsequent concl = do
    gs <- goalSequent <$> ask
    return $ isSubsequentOp concl gs
  subsumesGoal s = do
    gs <- goalSequent <$> ask
    return $ s `Prover.Structures.subsumesGoalOp` gs
