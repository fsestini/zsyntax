{-| This module is just a re-export of all the prover internals from other
    modules, for client code use. -}

module Prover
  ( proverSearch
  , SearchTriple(..)
  , SearchMonad(..)
  ) where

import Prover.Transformer
import Prover.Structures
import Prover.Class
import Prover.Search
