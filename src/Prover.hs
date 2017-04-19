{-| This module is just a re-export of all the prover internals from other
    modules, for client code use. -}

module Prover
  ( HasProverState(..)
  , HasProverEnvironment(..)
  , addInactives
  , addRules
  , removeSubsumedByAll
  , filterUnsubsumed
  , ProverT
  , runProverT
  , Stage(..)
  , SearchSequent
  , ActiveSequent
  , ActiveSequents
  , InactiveSequent
  , InactiveSequents
  , ConclSequent
  , Rule
  , RuleRes
  , initialSequentsAndRules
  , RuleAppRes
  , resRules
  , resSequents
  , applyAll
  , percolate
  , haveGoal
  , initialIsFSChecked
  , initialIsBSChecked
  , applyRule
  ) where

import Prover.Structures
import Prover.Class
import Prover.Transformer
