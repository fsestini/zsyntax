{-# LANGUAGE RankNTypes #-}

module Prover.Transformer where

import qualified Data.Map as M
import qualified Data.Set as S
import LabelledSequent
import Formula
import Rule
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import Prover.Class

type ActiveSequents l a = S.Set (ActiveSequent l a)
type InactiveSequents l a = S.Set (LabelledSequent l a)
newtype Formula a = F (forall p . LFormula p () a)

type ProverState l a = ([Rule l a], ActiveSequents l a, InactiveSequents l a)
type ProverEnvironment l a = (LabelledSequent l a, M.Map (Label l a) (Formula a))

type ProverT l a m b = ReaderT (ProverEnvironment l a) (StateT (ProverState l a) m) b
