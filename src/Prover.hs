{-| This module is just a re-export of all the prover internals from other
    modules, for client code use. -}

module Prover
  ( proverSearch
  , SearchPair(..)
  , SearchMonad(..)
  ) where

import Prover.Transformer
import Prover.Structures
import Prover.Class
import Prover.Search
