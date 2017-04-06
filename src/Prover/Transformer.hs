{-# LANGUAGE RankNTypes #-}

module Prover.Transformer where

import qualified Data.Map as M
import qualified Data.Set as S
import Formula
import Rule
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader

type ProverState l a = ([Rule l a], ActiveSequents l a, InactiveSequents l a)
type ProverEnvironment l a = (LabelledSequent l a, M.Map (Label l a) (Formula a))

newtype ActiveSequents l a = AS (S.Set (LabelledSequent l a))
newtype InactiveSequents l a = IS (S.Set (LabelledSequent l a))
newtype Formula a = F (forall p . LFormula p () a)

type ProverT l a m b = ReaderT (ProverEnvironment l a) (StateT (ProverState l a) m) b
