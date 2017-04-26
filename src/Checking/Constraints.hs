{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

{-# OPTIONS_GHC -Wall #-}

module Checking.Constraints where

import Formula
import Control.Monad

data Schema s l where
  Label :: l -> Schema s l
  Set :: s -> Schema s l
  Sum :: Schema s l -> Schema s l -> Schema s l
  deriving (Eq, Functor)

instance Applicative (Schema s) where
  pure = return
  (<*>) = ap

instance Monad (Schema s) where
  return = Label
  (Label l) >>= f = f l
  (Set x) >>= _ = Set x
  (Sum s1 s2) >>= f = Sum (s1 >>= f) (s2 >>= f)

type CSSchema l a = Schema (ControlSet a) l
type BCSchema l a = Schema (BiocoreSet a) l

data BioConstraint l a :: * where
  Respect :: BCSchema l a -> CSSchema l a -> BioConstraint l a
  And :: BioConstraint l a -> BioConstraint l a -> BioConstraint l a
  Or :: BioConstraint l a -> BioConstraint l a -> BioConstraint l a

-- | Equality constraints:
data EqConstraint s l = VarConstr l (Schema s l)
                      | SetConstr s (Schema s l)

type BioEqConstraint l a = EqConstraint (BiocoreSet a) l
type CtrlEqConstraint l a = EqConstraint (ControlSet a) l
