{-# LANGUAGE DataKinds #-}

module Main where

import SFormula
import RelFormula
import Prover
import Frontier
import Checking
import Context
import TypeClasses

main :: IO ()
main = undefined

test1 :: SFormula SimpleElemBase SimpleCtrlSet Int
test1 = sAtom (BioAtom 0)

test2 :: SFormula SimpleElemBase SimpleCtrlSet Int
test2 = sAtom (BioAtom 2)

test1' :: LFormula SimpleElemBase SimpleCtrlSet KImpl Int Int
test1' = Impl (Atom (BioAtom 0)) mempty mempty (Atom (BioAtom 2)) 2

test2' :: LFormula SimpleElemBase SimpleCtrlSet KImpl Int Int
test2' = Impl (Atom (BioAtom 0)) mempty mempty (Atom (BioAtom 0)) 2

type FFF = SFormula SimpleElemBase SimpleCtrlSet Int

llImpl x y = sImpl x mempty mempty y

atob :: FFF
atob = zero `llImpl` sAtom (BioAtom 1)

zero :: FFF
zero = sAtom (BioAtom 0)

--------------------------------------------------------------------------------

type SSS = Sequent SimpleElemBase SimpleCtrlSet Int

se :: SSS
se = SQ mempty (fromFoldable [atob, zero]) (sAtom (BioAtom 1))

nnn
  :: (PickMonad m l, Ord l)
  => m (GoalNeutralSequent SimpleElemBase SimpleCtrlSet Int l)
nnn = neutralize se Nothing
