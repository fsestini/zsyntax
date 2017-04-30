{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Prover.Frontier
  ( initialSequentsAndRules
  ) where

{-

  Given a goal Gamma ; Delta ===> Q, its frontier contains

  1. All top-level formulas in Gamma^-_! , Delta^-_. , and Q^+_.
  2. For any A in Gamma, Delta, the collection f(A)^-
  3. The collection f(Q)^+

-}

import TypeClasses (filterOut, partitionEithers)
import LabelledSequent
import Formula
import qualified Data.Set as S
import Relation
import Rel
import Control.Arrow
import DerivationTerm
import SFormula (fromLFormula)

--------------------------------------------------------------------------------
-- Decorated formulas

-- | Decoration kind.
data FShape = NonAtomic | LBNAtom | RBNAtom | LBPAtom | RBPAtom

type family NegFShape (b :: Bias) = (r :: FShape) | r -> b where
  NegFShape LeftBias = LBNAtom
  NegFShape RightBias = RBNAtom

type family PosFShape (b :: Bias) = (r :: FShape) | r -> b where
  PosFShape LeftBias = LBPAtom
  PosFShape RightBias = RBPAtom

class NonAtom (p :: Pole) where
instance NonAtom LSRA where
instance NonAtom LARS where

-- TODO: Don't I have to include polarity in the type?
data DecFormula :: FShape -> * -> * -> * where
  UnrestrNegativeAtom :: Atom b a -> DecFormula (NegFShape b) l a
  UnrestrNegative
    :: (NonAtom p)
    => LFormula p l a -> DecFormula NonAtomic l a
  LinearNegativeAtom :: Atom b a -> DecFormula (NegFShape b) l a
  LinearNegative :: LFormula LSRA l a -> DecFormula NonAtomic l a
  LinearPositiveAtom :: Atom b a -> DecFormula (PosFShape b) l a
  LinearPositive
    :: LFormula LARS l a -> DecFormula NonAtomic l a

data ODecFormula l a = forall s . ODF (DecFormula s l a)

instance Eq (ODecFormula l a) where
  (==) = undefined

instance Ord (ODecFormula l a) where
  compare = undefined

toUnrestrNeg :: OLFormula l a -> ODecFormula l a
toUnrestrNeg (OLF (FAtom a)) = ODF . UnrestrNegativeAtom $ a
toUnrestrNeg (OLF f@(FConj _ _ _)) = ODF . UnrestrNegative $ f
toUnrestrNeg (OLF f@(FImpl _ _ _)) = ODF . UnrestrNegative $ f

toLinearNeg :: OLSLFormula l a -> ODecFormula l a
toLinearNeg (OLSLF f) =
  case decideLS f of
    Left (OA atom) -> ODF . LinearNegativeAtom $ atom
    Right formula -> ODF . LinearNegative $ formula

toLinearPositive :: (IsRightSynchronous p) => LFormula p l a -> ODecFormula l a
toLinearPositive f =
  case decideRS f of
    Left (OA atom) -> ODF . LinearPositiveAtom $ atom
    Right formula -> ODF . LinearPositive $ formula

--------------------------------------------------------------------------------
-- Frontier computation

-- | Computes the frontier of a labelled sequent.
frontier :: NeutralSequent l a -> S.Set (ODecFormula l a)
frontier (NSQ uc lc goal) =
  S.map toUnrestrNeg uc `S.union` (S.fromList . map toLinearNeg) lc `S.union`
  S.singleton (toLinearPositive goal) `S.union`
  unrestrFrontier `S.union`
  linearFrontier `S.union`
  goalFrontier
  where
    unrestrFrontier = S.foldr S.union S.empty (S.map ofn uc)
    linearFrontier = foldr S.union S.empty (map olsfn lc)
    goalFrontier = frontierPositive goal

-- | Same as frontierNegative, but for opaque formulas.
ofn :: OLFormula l a -> S.Set (ODecFormula l a)
ofn (OLF f) = frontierNegative f

-- | Same as frontierNegative, but for opaque left-synchronous formulas.
olsfn :: OLSLFormula l a -> S.Set (ODecFormula l a)
olsfn (OLSLF f) = frontierNegative f

frontierNegative :: LFormula p l a -> S.Set (ODecFormula l a)
frontierNegative (FAtom (RBAtom _)) = S.empty
frontierNegative f@(FAtom a@(LBAtom _)) = S.singleton (ODF (LinearNegativeAtom a))
frontierNegative f@(FConj _ _ _) = activeNegative f
frontierNegative (FImpl f1 f2 _) =
  frontierPositive f1 `S.union` frontierNegative f2

frontierPositive :: LFormula p l a -> S.Set (ODecFormula l a)
frontierPositive f@(FAtom a@(RBAtom _)) = S.singleton (ODF (LinearPositiveAtom a))
frontierPositive (FAtom (LBAtom _)) = S.empty
frontierPositive (FConj f1 f2 _) =
  frontierPositive f1 `S.union` frontierPositive f2
frontierPositive f@(FImpl _ _ _) = activePositive f

activeNegative :: LFormula p l a -> S.Set (ODecFormula l a)
activeNegative (FAtom a) = S.singleton (ODF (LinearNegativeAtom a))
activeNegative (FConj f1 f2 _) = activeNegative f1 `S.union` activeNegative f2
activeNegative f@(FImpl _ _ _) =
  frontierNegative f `S.union` S.singleton (ODF (LinearNegative f))

activePositive :: LFormula p l a -> S.Set (ODecFormula l a)
activePositive (FAtom a) = S.singleton (ODF (LinearPositiveAtom a))
activePositive f@(FConj _ _ _) =
  frontierPositive f `S.union` S.singleton (ODF (LinearPositive f))
activePositive (FImpl f1 f2 _) = activeNegative f1 `S.union` activePositive f2

--------------------------------------------------------------------------------
-- Generation of initial rules from the frontier.

{-

We do not consider negative left-biased atoms (or positive right-biased atoms)
when constructing derived rules from the formulas in the frontier.

-}

data ThreeWay a b c = TOne a | TTwo b | TThree c

class Valid (s :: FShape) where
instance Valid NonAtomic where
instance Valid RBNAtom where
instance Valid LBPAtom where

data ValidDecFormula l a = forall s . (Valid s) => VDF (DecFormula s l a)

decideValid :: ODecFormula l a -> Maybe (ValidDecFormula l a)
decideValid (ODF decf) =
  case decf of
    UnrestrNegativeAtom (RBAtom _) -> Just . VDF $ decf
    UnrestrNegativeAtom (LBAtom _) -> Nothing
    UnrestrNegative _ -> Just . VDF $ decf
    LinearNegativeAtom (RBAtom _) -> Just . VDF $ decf
    LinearNegativeAtom (LBAtom _) -> Nothing
    LinearNegative _ -> Just . VDF $ decf
    LinearPositiveAtom (RBAtom _) -> Nothing
    LinearPositiveAtom (LBAtom _) -> Just . VDF $ decf
    LinearPositive _ -> Just . VDF $ decf

genRuleFromValid
  :: (Eq a, Eq l, Ord a, Ord l)
  => ValidDecFormula l a
  -> Rel (DLSequent l a) (DLSequent l a)
genRuleFromValid (VDF f) =
  case f of
    UnrestrNegativeAtom a -> unrestr (FAtom a)
    UnrestrNegative f -> unrestr f
    LinearNegativeAtom a -> linearNeg (FAtom a)
    LinearNegative f -> linearNeg f
    LinearPositiveAtom a -> linearPos (FAtom a)
    LinearPositive f -> linearPos f
  where
    unrestr formula = do
      (d, MRes gamma delta (LabelResult goal)) <- negativeFocalDispatch formula
      return $
        DLS
          (Copy d (label formula) (fromLFormula formula))
          (LS (add (label formula) gamma) delta goal)
    linearNeg formula = do
      (d, MRes gamma delta (LabelResult goal)) <- negativeFocalDispatch formula
      return $ DLS d (LS gamma (add (label formula) delta) goal)
    linearPos formula = do
      (d, MRes gamma delta _) <- positiveFocalDispatch formula
      return $ DLS d (LS gamma delta (label formula))

--------------------------------------------------------------------------------
-- Main function

initialSequentsAndRules
  :: (Eq a, Eq l, Ord l, Ord a)
  => NeutralSequent l a
  -> (S.Set (DLSequent l a),
       [(DLSequent l a -> Rel (DLSequent l a) (DLSequent l a))])
initialSequentsAndRules =
  frontier >>>
  S.toList >>>
  map decideValid >>>
  filterOut >>>
  map genRuleFromValid >>>
  map unRel >>>
  filterOut >>>
  partitionEithers >>>
  (S.fromList
  *** id)
