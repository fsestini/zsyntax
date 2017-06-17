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
import Formula
import Rel (Rel)
import Control.Monad.Trans.State.Lazy hiding (get, put)
import Control.Monad.Trans.Reader hiding (ask)
import Data.Foldable

import ForwardSequent
import TypeClasses hiding (map)
import Data.Profunctor

import Prover.Class
import Prover.Structures
import Prover.Search

--------------------------------------------------------------------------------

proverSearch'
  :: ( Ord seqty
     , Monad m
     , SearchMonad mf
     , SearchTriple seqty goalty proof
     , Foldable f
     )
  => f seqty -> [seqty -> Rel seqty seqty] -> ProverT seqty goalty m (mf proof)
proverSearch' seqs rules =
  doSearch
    (S.fromList . fmap initialize . toList $ seqs)
    (map toProverRules rules)

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
deriving instance
         (Monad m) =>
         MonadState (ProverState seqty) (ProverT seqty goalty m)
deriving instance
         (Monad m) =>
         MonadReader (ProverEnvironment goalty) (ProverT seqty goalty m)

instance (Monad m, Ord seqty, ForwardSequent seqty) =>
         HasProverState seqty (ProverT seqty goalty m) where
  getRules = rules <$> get
  addRule r = do
    (PS rls as is gi) <- get
    put (PS (r : rls) as is gi)
  addInactive i = do
    (PS r as is gi) <- get
    let (newIs, newInd) = addToInactives is gi i
    put (PS r as newIs newInd)
  popInactive = do
    (PS r as is gi) <- get
    case popInactiveOp is of
      Right (newIs, inactive) -> do
        let (newAs, active) = activate as inactive
        put (PS r newAs newIs gi)
        return . Right $ active
      Left r -> return . Left $ r
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

instance (Monad m, SearchTriple seqty goalty proof) =>
         HasProverEnvironment seqty proof (ProverT seqty goalty m) where
  subsumesGoal s = do
    (e :: ProverEnvironment goalty) <- ask
    return $ s `Prover.Structures.subsumesGoalOp` (goalSequent e)
