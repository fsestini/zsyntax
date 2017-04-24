{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module ControlSet where

import qualified Data.Set as S
import Formula

type ControlSet a = S.Set (BioFormula a)
type ContextSet a = S.Set (BioFormula a)

-- Control Set schema
data CSSchema l a :: * where
  CSLabel :: l -> CSSchema l a -- Control sets
  CSSet   :: ControlSet a -> CSSchema l a
  CSSum   :: CSSchema l a -> CSSchema l a -> CSSchema l a

-- Bio-core Set schema
data BCSchema l a :: * where
  BCLabel :: l -> BCSchema l a -- Bio-core sets
  BCSet   :: ContextSet a -> BCSchema l a
  BCSum   :: BCSchema l a -> BCSchema l a -> BCSchema l a

data EqConstraint l a = CSEC l (CSSchema l a)
                      | BCEC l (BCSchema l a)

data ControlConstraint l a :: * where
  Respect :: BCSchema l a -> CSSchema l a -> ControlConstraint l a
  And :: ControlConstraint l a -> ControlConstraint l a -> ControlConstraint l a
  Or :: ControlConstraint l a -> ControlConstraint l a -> ControlConstraint l a
