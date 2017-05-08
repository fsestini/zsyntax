{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Frontier where
  -- ( initialSequentsAndRules
  -- ) where

{-

  Given a goal Gamma ; Delta ===> Q, its frontier contains

  1. All top-level formulas in Gamma^-_! , Delta^-_. , and Q^+_.
  2. For any A in Gamma, Delta, the collection f(A)^-
  3. The collection f(Q)^+

-}

import Data.Foldable
import Data.Monoid
import TypeClasses (filterOut, partitionEithers)
import LabelledSequent
import RelFormula
import qualified Data.Set as S
import Relation
import Rel
import Control.Arrow
-- import DerivationTerm
-- import SFormula (fromLFormula)
import Context

--------------------------------------------------------------------------------
-- Decorated formulas

-- | Decoration kind.
data FShape = NonAtomic | LBNAtom | RBNAtom | LBPAtom | RBPAtom

-- type family NegFShape (b :: Bias) = (r :: FShape) | r -> b where
--   NegFShape LeftBias = LBNAtom
--   NegFShape RightBias = RBNAtom

-- type family PosFShape (b :: Bias) = (r :: FShape) | r -> b where
--   PosFShape LeftBias = LBPAtom
--   PosFShape RightBias = RBPAtom

-- class NonAtom (p :: Pole) where
-- instance NonAtom LSRA where
-- instance NonAtom LARS where

-- | Decorated formulas
data DecFormula :: (* -> *) -> (* -> *) -> * -> * -> * where
  Unrestr :: Axiom eb cs a l -> DecFormula eb cs a l
  --LinearNegativeAtom :: Atom b a -> DecFormula (NegFShape b) a l
  LinearNegative :: ImplFormula eb cs IRegular a l -> DecFormula eb cs a l
  --LinearPositiveAtom :: Atom b a -> DecFormula (PosFShape b) a l
  LinearPositive :: OLFormula eb cs a l -> DecFormula eb cs a l
  deriving (Eq, Ord)

-- instance (Ord a, Ord l) => Eq (ODecFormula a l) where
--   (ODF f1) == (ODF f2) = compareODec f1 f2 == EQ

-- instance (Ord a, Ord l) => Ord (ODecFormula a l) where
--   compare (ODF f1) (ODF f2) = compareODec f1 f2

-- -- unrnegatom < unrneg < linnegatom < linneg < linposatom < linpos-}
-- compareODec :: (Ord a, Ord l) => DecFormula s1 a l -> DecFormula s2 a l -> Ordering
-- compareODec (UnrestrNegativeAtom a1) (UnrestrNegativeAtom a2) = compareAtom a1 a2
-- compareODec (UnrestrNegative f1) (UnrestrNegative f2) = compareLF f1 f2
-- compareODec (LinearNegativeAtom a1) (LinearNegativeAtom a2) = compareAtom a1 a2
-- compareODec (LinearNegative f1) (LinearNegative f2) = compareLF f1 f2
-- compareODec (LinearPositiveAtom a1) (LinearPositiveAtom a2) = compareAtom a1 a2
-- compareODec (LinearPositive f1) (LinearPositive f2) = compareLF f1 f2
-- compareODec (UnrestrNegativeAtom _) _ = LT
-- compareODec (UnrestrNegative _) (UnrestrNegativeAtom _) = GT
-- compareODec (UnrestrNegative _) _ = LT
-- compareODec (LinearNegativeAtom _) (UnrestrNegativeAtom _) = GT
-- compareODec (LinearNegativeAtom _) (UnrestrNegative _) = GT
-- compareODec (LinearNegativeAtom _) _ = LT
-- compareODec (LinearNegative _) (UnrestrNegativeAtom _) = GT
-- compareODec (LinearNegative _) (UnrestrNegative _) = GT
-- compareODec (LinearNegative _) (LinearNegativeAtom _) = GT
-- compareODec (LinearNegative _) _ = LT
-- compareODec (LinearPositiveAtom _) (UnrestrNegativeAtom _) = GT
-- compareODec (LinearPositiveAtom _) (UnrestrNegative _) = GT
-- compareODec (LinearPositiveAtom _) (LinearNegativeAtom _) = GT
-- compareODec (LinearPositiveAtom _) (LinearNegative _) = GT
-- compareODec (LinearPositiveAtom _) _ = LT
-- compareODec (LinearPositive _) _ = GT

-- toUnrestrNeg :: OLFormula a l -> ODecFormula a l
-- toUnrestrNeg (OLF (FAtom a)) = ODF . UnrestrNegativeAtom $ a
-- toUnrestrNeg (OLF f@(FConj _ _ _)) = ODF . UnrestrNegative $ f
-- toUnrestrNeg (OLF f@(FImpl _ _ _)) = ODF . UnrestrNegative $ f

-- toLinearNeg :: OLSLFormula a l -> ODecFormula a l
-- toLinearNeg (OLSLF f) =
--   case decideLS f of
--     Left (OA atom) -> ODF . LinearNegativeAtom $ atom
--     Right formula -> ODF . LinearNegative $ formula

-- toLinearPositive :: (IsRightSynchronous p) => LFormula p a l -> ODecFormula a l
-- toLinearPositive f =
--   case decideRS f of
--     Left (OA atom) -> ODF . LinearPositiveAtom $ atom
--     Right formula -> ODF . LinearPositive $ formula

--------------------------------------------------------------------------------
-- Frontier computation

filterImpl :: [NeutralFormula eb cs a l] -> [ImplFormula eb cs IRegular a l]
filterImpl = filterOut . map aux
  where
    aux :: NeutralFormula eb cs a l -> Maybe (ImplFormula eb cs IRegular a l)
    aux (NF (Impl' f)) = Just f
    aux _ = Nothing

-- | Computes the frontier of a labelled sequent.
frontier
  :: forall a l eb cs . (Ord a, Ord l, ElemBase eb a)
  => NeutralSequent eb cs a l -> S.Set (DecFormula eb cs a l)
frontier (NS uc lc _ (OLF goal)) =
  toplevelUC <> toplevelLC <> S.singleton (LinearPositive (OLF goal)) <>
  ucFrontier <>
  linFrontier <>
  goalFrontier
  where
    toplevelUC = (S.fromList . map Unrestr . asFoldable toList $ uc)
    toplevelLC =
      (S.fromList . map LinearNegative . filterImpl . asFoldable toList $ lc)
    ucFrontier =
      fold . map (frNeg . NF . axiomIsFormula) . asFoldable toList $ uc
    linFrontier = fold . map frNeg . asFoldable toList $ lc
    goalFrontier = frPos goal

frNeg :: Ord l => NeutralFormula eb cs a l -> S.Set (DecFormula eb cs a l)
frNeg f@(NF (Atom _)) = mempty
frNeg f@(NF (Impl a _ _ b _)) = foc a <> act b

frPos :: Ord l => LFormula eb cs k a l -> S.Set (DecFormula eb cs a l)
frPos (Atom _) = mempty
frPos f@(Conj _ _ _) = foc f
frPos (Impl a _ _ b _) =
  act a <> frPos b <> S.singleton (LinearPositive (OLF b))

foc :: Ord l => LFormula eb cs k a l -> S.Set (DecFormula eb cs a l)
foc (Atom _) = mempty
foc (Conj f1 f2 _) = foc f1 <> foc f2
foc f@(Impl _ _ _ _ _) = S.singleton (LinearPositive (OLF f)) <> frPos f

act :: Ord l => LFormula eb cs k a l -> S.Set (DecFormula eb cs a l)
act a@(Atom _) = mempty
act (Conj a b _) = act a <> act b
act f@(Impl' impl) = S.singleton (LinearNegative impl) <> frNeg (NF f)

--------------------------------------------------------------------------------
-- Generation of initial rules from the frontier.

-- We do not consider negative atoms when constructing derived rules from the
-- formulas in the frontier.

-- data ThreeWay a b c = TOne a | TTwo b | TThree c

-- class Valid (s :: FShape) where
-- instance Valid NonAtomic where
-- instance Valid RBNAtom where
-- instance Valid LBPAtom where

-- data ValidDecFormula a l = forall s . (Valid s) => VDF (DecFormula s a l)

-- decideValid :: ODecFormula a l -> Maybe (ValidDecFormula a l)
-- decideValid (ODF decf) =
--   case decf of
--     UnrestrNegativeAtom (RBAtom _) -> Just . VDF $ decf
--     UnrestrNegativeAtom (LBAtom _) -> Nothing
--     UnrestrNegative _ -> Just . VDF $ decf
--     LinearNegativeAtom (RBAtom _) -> Just . VDF $ decf
--     LinearNegativeAtom (LBAtom _) -> Nothing
--     LinearNegative _ -> Just . VDF $ decf
--     LinearPositiveAtom (RBAtom _) -> Nothing
--     LinearPositiveAtom (LBAtom _) -> Just . VDF $ decf
--     LinearPositive _ -> Just . VDF $ decf

generateRule
  :: (BaseCtrl eb cs a, Ord l, Ord a)
  => DecFormula eb cs a l
  -> Rel (NeutralSequent eb cs a l) (NeutralSequent eb cs a l)
generateRule f =
  case f of
    Unrestr axiom -> copyRule axiom
    LinearNegative impl -> implLeft impl
    LinearPositive (OLF orf) ->
      case orf of
        Atom _ -> focus orf
        Conj _ _ _ -> focus orf
        Impl' impl -> implRight impl

-- --------------------------------------------------------------------------------
-- -- Main function

type UnaryRule eb cs a l = NeutralSequent eb cs a l -> Rule eb cs a l

initialSequentsAndRules
  :: (Eq a, Eq l, Ord l, Ord a, BaseCtrl eb cs a, Ord (cs a))
  => NeutralSequent eb cs a l
  -> (S.Set (NeutralSequent eb cs a l), [UnaryRule eb cs a l])
initialSequentsAndRules =
  frontier >>>
  S.toList >>>
  map generateRule >>>
  map unRel >>>
  filterOut >>>
  partitionEithers >>>
  (S.fromList *** id)

-- initialSequentsAndRules
--   :: (Eq a, Eq l, Ord l, Ord a)
--   => NeutralSequent a l
--   -> (S.Set (DLSequent a l),
--        [(DLSequent a l -> Rel (DLSequent a l) (DLSequent a l))])
-- initialSequentsAndRules =
--   frontier >>>
--   S.toList >>>
--   map decideValid >>>
--   filterOut >>>
--   map genRuleFromValid >>>
--   map unRel >>>
--   filterOut >>>
--   partitionEithers >>>
--   (S.fromList
--   *** id)
