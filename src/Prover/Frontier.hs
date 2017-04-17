{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Prover.Frontier
  ( frontierNegative
  , frontierPositive
  , DecLFormula(..)
  ) where

{-

  Given a goal Gamma ; Delta ===> Q, its frontier contains

  1. All top-level formulas in Gamma^-_! , Delta^-_. , and Q^+_.
  2. For any A in Gamma, Delta, the collection f(A)^-
  3. The collection f(Q)^+

-}

import Formula
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- Decorated formulas

data DecLFormula :: * -> * -> * where
  UnrestrDLF :: LFormula p l a -> DecLFormula l a
  LinearNegativeDLF
    :: (IsLeftSynchronous p)
    => LFormula p l a -> DecLFormula l a
  LinearPositiveDLF
    :: (IsRightSynchronous p)
    => LFormula p l a -> DecLFormula l a

instance Eq (DecLFormula l a) where
  (==) = undefined

instance Ord (DecLFormula l a) where
  compare = undefined

frontierNegative :: LFormula p l a -> S.Set (DecLFormula l a)
frontierNegative (FAtom (RBAtom _)) = S.empty
frontierNegative f@(FAtom (LBAtom _)) = S.singleton (LinearNegativeDLF f)
frontierNegative f@(FConj _ _ _) = activeNegative f
frontierNegative (FImpl f1 f2 _) =
  frontierPositive f1 `S.union` frontierNegative f2

frontierPositive :: LFormula p l a -> S.Set (DecLFormula l a)
frontierPositive f@(FAtom (RBAtom _)) = S.singleton (LinearPositiveDLF f)
frontierPositive (FAtom (LBAtom _)) = S.empty
frontierPositive (FConj f1 f2 _) =
  frontierPositive f1 `S.union` frontierPositive f2
frontierPositive f@(FImpl _ _ _) = activePositive f

activeNegative :: LFormula p l a -> S.Set (DecLFormula l a)
activeNegative f@(FAtom _) = S.singleton (LinearNegativeDLF f)
activeNegative (FConj f1 f2 _) = activeNegative f1 `S.union` activeNegative f2
activeNegative f@(FImpl _ _ _) =
  frontierNegative f `S.union` S.singleton (LinearNegativeDLF f)

activePositive :: LFormula p l a -> S.Set (DecLFormula l a)
activePositive f@(FAtom _) = S.singleton (LinearPositiveDLF f)
activePositive f@(FConj _ _ _) =
  frontierPositive f `S.union` S.singleton (LinearPositiveDLF f)
activePositive (FImpl f1 f2 _) = activeNegative f1 `S.union` activePositive f2