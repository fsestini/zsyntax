{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module LFormula
  ( GoalNSequent(..)
  , BioFormula(..)
  , LFormula(..)
  , BFormula(..)
  , LAxiom(..)
  , Label(..)
  , SrchFormula(..)
  , SrchNeutral(..)
  , SrchOpaque
  , SrchAxiom(..)
  , LGoalNSequent
  , LResultNSequent
  , LNSequent
  , LUnaryRule
  , LDTSequent
  , mapEbCty
  , mapCtyAx
  , opaque
  , label
  , axToFormula
  , liftComplexity
  , deepHetCompare
  , maybeNeutral
  , decideOF
  , decideF
  , decideN
  ) where

import Rules
import qualified TypeClasses as T
import Data.Constraint
import Data.Function (on)
import TH

-- Formula complexity
data FComp = CBasic | CComplex

{-| The type of biological (and non-logical) formulas, which constitute
    the logical atoms.
    It is parameterized over the type of biological atoms. -}
data BioFormula a  =  BioAtom a
                   |  BioInter (BioFormula a) (BioFormula a)
                   deriving (Functor, Foldable, Show)

-- | Custom equality instance for biological atoms.
-- It witnesses commutativity of the biological interaction operator.
instance Ord a => Eq (BioFormula a) where
  bf1 == bf2 = compare bf1 bf2 == EQ

instance Ord a =>
         Ord (BioFormula a) where
  compare (BioAtom a1) (BioAtom a2) = compare a1 a2
  compare (BioInter bf1 bf2) (BioInter bf1' bf2') =
    if (bf1 == bf1' && bf2 == bf2') || (bf1 == bf2' && bf2 == bf1')
      then EQ
      else compare bf1 bf1' `comb` compare bf2 bf2'
    where
      comb :: Ordering -> Ordering -> Ordering
      comb EQ x = x
      comb x _ = x
  compare (BioAtom _) (BioInter _ _) = LT
  compare (BioInter _ _) (BioAtom _) = GT

instance T.Pretty a => T.Pretty (BioFormula a) where
  pretty (BioAtom x) = T.pretty x
  pretty (BioInter x y) = "(" ++ T.pretty x ++ "<>" ++ T.pretty y ++ ")"

data LFormula :: * -> * -> FKind -> FComp -> * -> * -> * where
  Atom :: BioFormula a -> LFormula eb cty KAtom c a l
  Conj
    :: LFormula eb cty k1 c a l
    -> LFormula eb cty k2 c a l
    -> l
    -> LFormula eb cty KConj c a l
  Impl
    :: LFormula eb cty k1 c a l
    -> eb
    -> cty
    -> LFormula eb cty k2 c a l
    -> l
    -> LFormula eb cty KImpl CComplex a l

deriving instance Functor (LFormula eb cs k c a)
deriving instance Foldable (LFormula eb cs k c a)
deriving instance Traversable (LFormula eb cs k c a)

instance T.Pretty a => T.Pretty (LFormula eb cty k c a l) where
  pretty (Atom x) = T.pretty x
  pretty (Conj f1 f2 _) = T.pretty f1 ++ " ⊗ " ++ T.pretty f2
  pretty (Impl f1 _ _ f2 _) = "(" ++ T.pretty f1 ++ " → " ++ T.pretty f2 ++ ")"

--------------------------------------------------------------------------------
-- Basic formulas

data BFormula a l = forall k . BF (LFormula () () k CBasic a l)
deriving instance Functor (BFormula a)
deriving instance Foldable (BFormula a)
deriving instance Traversable (BFormula a)

-- fromBasicLFormula :: LFormula eb cty k CBasic a l -> BFormula a l
-- fromBasicLFormula f = BF (mapEbCty (const ()) (const ()) f)

bfToAtoms :: LFormula eb cs k CBasic a l -> [BioFormula a]
bfToAtoms (Atom x) = [x]
bfToAtoms (Conj f1 f2 _) = bfToAtoms f1 ++ bfToAtoms f2

decideF :: LFormula eb cty k c a l -> Maybe (BFormula a l)
decideF (Atom x) = Just (BF (mapEbCty (const ()) (const ()) (Atom x)))
decideF (Conj f1 f2 l) = do
  (BF f1b) <- decideF f1
  (BF f2b) <- decideF f2
  return (BF (mapEbCty (const ()) (const ()) (Conj f1b f2b l)))
decideF (Impl _ _ _ _ _) = Nothing

decideN
  :: (Ord a, Ord l)
  => Neutral (SrchFormula eb cty a l) -> Maybe (BFormula a l)
decideN (switchN -> Left (AR x _)) = Just (BF (Atom x))
decideN (switchN -> Right (IR _ _ _ _ _)) = Nothing

-- TODO temporary hack
decideOF :: Opaque (SrchFormula eb cty a l) -> Maybe (BFormula a l)
decideOF (O (Srch f)) = decideF f

--------------------------------------------------------------------------------

data LAxiom cty a l = LAx (BFormula a l) cty (BFormula a l) l

deriving instance Functor (LAxiom cty a)
deriving instance Foldable (LAxiom cty a)
deriving instance Traversable (LAxiom cty a)

axToFormula :: Monoid cty => LAxiom cty a l -> LFormula () cty KImpl CComplex a l
axToFormula (LAx (BF f1) cty (BF f2) l) =
  Impl
    (mapEbCty (const mempty) (const mempty) f1)
    mempty
    cty
    (mapEbCty (const mempty) (const mempty) f2)
    l

data Label a l = L l | A (BioFormula a) deriving (Eq, Ord, Show)

label :: LFormula eb cs k c a l -> Label a l
label (Atom a) = A a
label (Conj _ _ lbl) = L lbl
label (Impl _ _ _ _ lbl) = L lbl

--------------------------------------------------------------------------------
-- Mapping functions

frmlMapAtoms
  :: (T.CanMap' eb a1 a2, T.CanMap' cty a1 a2)
  => (a1 -> a2) -> LFormula eb cty k c a1 l -> LFormula eb cty k c a2 l
frmlMapAtoms f (Atom b) = Atom (fmap f b)
frmlMapAtoms f (Conj f1 f2 l) = Conj (frmlMapAtoms f f1) (frmlMapAtoms f f2) l
frmlMapAtoms f (Impl f1 eb cty f2 l) =
  Impl (frmlMapAtoms f f1) (T.map' f eb) (T.map' f cty) (frmlMapAtoms f f2) l

mapEbCty
  :: (eb1 -> eb2)
  -> (cty1 -> cty2)
  -> LFormula eb1 cty1 k c a l
  -> LFormula eb2 cty2 k c a l
mapEbCty f g (Atom a) = Atom a
mapEbCty f g (Conj f1 f2 l) = Conj (mapEbCty f g f1) (mapEbCty f g f2) l
mapEbCty f g (Impl f1 eb cty f2 l) =
  Impl (mapEbCty f g f1) (f eb) (g cty) (mapEbCty f g f2) l

mapCtyAx :: (cty1 -> cty2) -> LAxiom cty1 a l -> LAxiom cty2 a l
mapCtyAx f (LAx (BF f1) cty (BF f2) l) =
  LAx (BF (mapEbCty id id f1)) (f cty) (BF (mapEbCty id id f2)) l

liftComplexity :: LFormula eb cs k c a l -> LFormula eb cs k CComplex a l
liftComplexity (Atom x) = Atom x
liftComplexity (Conj f1 f2 l) = Conj (liftComplexity f1) (liftComplexity f2) l
liftComplexity (Impl f1 eb cty f2 l) =
  Impl (liftComplexity f1) eb cty (liftComplexity f2) l

--------------------------------------------------------------------------------
-- Deep heterogeneous comparison functions

deepHetCompare
  :: (Ord a, Ord l, Ord eb, Ord cs)
  => LFormula eb cs k1 c1 a l -> LFormula eb cs k2 c2 a l -> Ordering
deepHetCompare (Atom x1) (Atom x2) = compare x1 x2
deepHetCompare (Atom _) _ = LT
deepHetCompare (Conj a1 b1 lbl1) (Conj a2 b2 lbl2) =
  if ca == EQ
    then if cb == EQ
           then cl
           else cb
    else ca
  where
    ca = deepHetCompare a1 a2
    cb = deepHetCompare b1 b2
    cl = compare lbl1 lbl2
deepHetCompare (Conj _ _ _) (Atom _) = GT
deepHetCompare (Conj _ _ _) (Impl _ _ _ _ _) = LT
deepHetCompare (Impl a1 eb1 cs1 b1 l1) (Impl a2 eb2 cs2 b2 l2) =
  if ca == EQ
    then if cb == EQ
           then if ceb == EQ
                  then if ccs == EQ
                         then cl
                         else ccs
                  else ceb
           else cb
    else ca
  where
    ca = deepHetCompare a1 a2
    cb = deepHetCompare b1 b2
    ceb = compare eb1 eb2
    ccs = compare cs1 cs2
    cl = compare l1 l2
deepHetCompare (Impl _ _ _ _ _) _ = GT

--------------------------------------------------------------------------------

-- | Type of labelled formulas to be used during proof search.
data SrchFormula eb cty a l k = forall c . Srch (LFormula eb cty k c a l)
newtype SrchAxiom cty a l = SrchAx { unSrchAx :: LAxiom cty a l }
type SrchNeutral eb cty a l = Neutral (SrchFormula eb cty a l)
type SrchOpaque eb cty a l = Opaque (SrchFormula eb cty a l)
type LGoalNSequent eb cty a l =
  GoalNSequent (SrchAxiom cty a l) (SrchFormula eb cty a l)
type LResultNSequent eb cty a l =
  ResultNSequent (SrchAxiom cty a l) (SrchFormula eb cty a l) cty
type LNSequent eb cty a l =
  NSequent (SrchAxiom cty a l) (SrchFormula eb cty a l) cty
-- type UnaryRule term fr = DTS term fr -> Rule term fr
type LUnaryRule term eb cty a l =
  UnaryRule term (SrchFormula eb cty a l)
type LDTSequent term eb cty a l =
  DT term (NSequent (SrchAxiom cty a l) (SrchFormula eb cty a l) cty)

liftUnifun 'Srch 'frmlMapAtoms
liftUnifun 'SrchAx 'mapCtyAx
liftBifun 'Srch 'mapEbCty

instance (Ord a, Eq l, Monoid cty) => Eq (SrchAxiom cty a l) where
  (==) = on (==) (label . axToFormula . unSrchAx)
instance (Ord a, Ord l, Monoid cty) => Ord (SrchAxiom cty a l) where
  compare = on compare (label . axToFormula . unSrchAx)

instance AtomClss (SrchFormula eb cty a l) where
  type AtomPayload (SrchFormula eb cty a l) = ()
  type AtomType (SrchFormula eb cty a l) = (BioFormula a)
  reprAtom (Srch (Atom a)) = AR a ()
  atom () a = Srch (Atom a)

instance ConjClss (SrchFormula eb cty a l) where
  type ConjPayload (SrchFormula eb cty a l) = l
  reprConj (Srch (Conj f1 f2 l)) = CR (Srch f1) (Srch f2) l
  conj (Srch f1) (Srch f2) l = Srch (Conj (liftComplexity f1) (liftComplexity f2) l)

instance ImplClss (SrchFormula eb cty a l) where
  type ImplPayload (SrchFormula eb cty a l) = l
  type Eb (SrchFormula eb cty a l) = eb
  type Cty (SrchFormula eb cty a l) = cty
  reprImpl (Srch (Impl f1 eb cty f2 l)) = IR (Srch f1) eb cty (Srch f2) l
  impl (Srch f1) eb cty (Srch f2) l =
    Srch (Impl (liftComplexity f1) eb cty (liftComplexity f2) l)

instance AxiomClss (SrchAxiom cty a l) where
  type SideFrml (SrchAxiom cty a l) = BFormula a l
  type AxPayload (SrchAxiom cty a l) = l
  type AxCty (SrchAxiom cty a l) = cty
  reprAx (SrchAx (LAx f1 cty f2 l)) = AxR f1 cty f2 l

instance (Ord a, Ord l) => Formula (SrchFormula eb cty a l) where
  cases (Srch (Atom a)) = AtomCase Dict
  cases (Srch (Conj _ _ _)) = ConjCase Dict
  cases (Srch (Impl _ _ _ _ _)) = ImplCase Dict
  hetCompare (Srch f1) (Srch f2) = compare (label f1) (label f2)

instance (Monoid eb, Monoid cty) =>
         HasAxiom (SrchFormula eb cty a l) where
  type Ax (SrchFormula eb cty a l) = SrchAxiom cty a l
  axIsFormula ax = Srch (mapEbCty (const mempty) id . axToFormula . unSrchAx $ ax)
