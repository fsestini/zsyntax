{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module RelFormula where

import LinearContext
import UnrestrContext
import Data.Foldable

--------------------------------------------------------------------------------
{- Datatype of formulas, parameterized by the type of
   - Elementary bases
   - Control sets
   - Labels
   - Biological atoms
-}

data FKind = KAtom | KConj | KImpl

data RelFormula :: (* -> *) -> (* -> *) -> FKind -> * -> * -> * where
  Atom :: a -> RelFormula eb cs KAtom l a
  Conj
    :: RelFormula eb cs k1 l a
    -> RelFormula eb cs k2 l a
    -> l
    -> RelFormula eb cs KConj l a
  Impl
    :: RelFormula eb cs k1 l a
    -> eb a
    -> cs a
    -> RelFormula eb cs k2 l a
    -> l
    -> RelFormula eb cs KImpl l a

instance Eq (RelFormula eb cs k l a) where
instance Ord (RelFormula eb cs k l a) where

-- | Opaque formulas
data ORelFormula eb cs l a = forall k . ORF (RelFormula eb cs k l a)

instance Eq (ORelFormula eb cs l a) where
instance Ord (ORelFormula eb cs l a) where

--------------------------------------------------------------------------------
-- Elementary bases and control sets

class (ControlSet cs a, ElemBase eb a) =>
      BaseCtrl eb cs a where
  respects :: eb a -> cs a -> Bool

class (Monoid (cs a), Eq (cs a)) =>
      ControlSet cs a

-- | Typeclass of elementary bases
class (Monoid (eb a), Eq (eb a)) =>
      ElemBase eb a where
  singleton :: a -> eb a

elemBase
  :: ElemBase eb a
  => NeutralFormula eb cs l a -> eb a
elemBase (NF (Atom a)) = singleton a
-- elemBase (NF (Conj f1 f2 _)) = elemBase (NF f1) `mappend` elemBase (NF f2)
elemBase (NF (Impl _ eb _ _ _)) = eb

elemBaseAll
  :: (ElemBase eb a, Foldable f)
  => f (NeutralFormula eb cs l a) -> eb a
elemBaseAll = fold . map elemBase . toList

--------------------------------------------------------------------------------
-- Neutral formulas and sequents

class IsNeutral (k :: FKind) where
instance IsNeutral KAtom where
instance IsNeutral KImpl where

data NeutralFormula eb cs l a =
  forall (k :: FKind) . IsNeutral k =>
            NF (RelFormula eb cs k l a)

instance Eq (NeutralFormula eb cs l a) where
instance Ord (NeutralFormula eb cs l a) where

type UCtxt eb cs l a = UnrestrCtxt (ORelFormula eb cs l a)
type LCtxt eb cs l a = LinearCtxt (NeutralFormula eb cs l a)

data NeutralLabelledSequent eb cs l a =
  NLS (UCtxt eb cs l a)
      (LCtxt eb cs l a)
      (cs a)
      (ORelFormula eb cs l a)
