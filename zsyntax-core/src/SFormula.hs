{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}

module SFormula
  ( Sequent(..)
  , SFormula(..)
  , LFormula(..)
  , SAxiom(..)
  , BioFormula(..)
  , BSFormula
  , sAtom
  , sConj
  , sImpl
  , neutralize
  , fromSrch
  , sAx
  , bsConj
  , bsAtom
  , fromBasicNS
  , srchAxToSax
  ) where

  -- ( SFormula(..)
  -- , BSFormula(..)
  -- , SAxiom(..)
  -- , Sequent(..)
  -- , fromNF
  -- , sAtom
  -- , fromBasicNS
  -- , sConj
  -- , sImpl
  -- , neutralize
  -- , sAxiomIsSFormula
  -- , fromLFormula
  -- , fromLAxiom
  -- , BioFormula(..)
  -- , LFormula(..)
  -- , OLFormula(..)
  -- , ElemBase(..)
  -- , ControlSet(..)
  -- , bsAtom
  -- , bsConj
  -- , sAx
  -- , pattern Impl
  -- ) where

import Control.Arrow ((>>>))
import Data.Bifunctor (bimap)
import LFormula
import TypeClasses (PickMonad(..), Pretty(..))
import Control.Monad
import qualified Data.Set as S
import UnrestrContext
import LinearContext
import Data.Foldable
import qualified TypeClasses as T
import qualified Data.List.NonEmpty as NE

--------------------------------------------------------------------------------
-- Basic simple formulas

type BSFormula a = BFormula a ()
  --forall k . BSF (LFormula U cs k CBasic a ())
newtype SAxiom cs a = SA {unSA :: (LAxiom cs a ())}

bsAtom :: BioFormula a -> BSFormula a
bsAtom x = BF (Atom x)

bsConj :: BSFormula a -> BSFormula a -> BSFormula a
bsConj (BF f1) (BF f2) = BF (Conj f1 f2 ())

sAx :: BSFormula a -> BSFormula a -> cty -> SAxiom cty a
sAx f1 f2 cs = SA (LAx f1 cs f2 ())

--------------------------------------------------------------------------------
-- Simple formulas

data SFormula eb cs a = forall k c . SF (LFormula eb cs k c a ())
newtype NSFormula eb cty a = NSF
  { unNSF :: (SrchNeutral eb cty a ())
  } --deriving (Show)

instance Pretty a => Pretty (SFormula eb cty a) where
  pretty (SF f) = pretty f

-- sAx :: SFormula eb cs a -> SFormula eb cs a -> cs a -> SAxiom cs a
-- sAx (SF (OLF f1)) (SF (OLF f2)) cs = SA (ImplF f1 EmptySpot cs f2 ())

-- instance Show a => Show (SFormula eb cs a) where
--   show (SF (OLF f)) = deepShowFormula f

-- deriving instance (Show a, Show (cs a)) => Show (SAxiom cs a)

-- instance Show a => Show (SAxiom cs a) where
--   show (SA ax) = deepShowImpl ax

instance (Ord a, Ord eb, Ord cs) => Eq (SFormula eb cs a) where
  (SF f1) == (SF f2) = deepHetCompare f1 f2 == EQ

instance (Ord a, Ord eb, Ord cs) => Ord (SFormula eb cs a) where
  compare (SF f1) (SF f2) = deepHetCompare f1 f2

instance (Ord a, Ord cty, Monoid cty) => Eq (SAxiom cty a) where
  (SA ax1) == (SA ax2) =
    deepHetCompare (axToFormula ax1) (axToFormula ax2) == EQ

instance (Ord a, Ord cty, Monoid cty) => Ord (SAxiom cty a) where
  compare (SA ax1) (SA ax2) =
    deepHetCompare (axToFormula ax1) (axToFormula ax2)

sAtom :: BioFormula a -> SFormula eb cs a
sAtom = SF . Atom

sConj :: SFormula eb cs a -> SFormula eb cs a -> SFormula eb cs a
sConj (SF f1) (SF f2) =
  lToS (Conj (liftComplexity f1) (liftComplexity f2) ())

sImpl :: SFormula eb cs a
      -> eb
      -> cs
      -> SFormula eb cs a
      -> SFormula eb cs a
sImpl (SF f1) eb cs (SF f2) =
  SF (Impl (liftComplexity f1) eb cs (liftComplexity f2) ())

lToS :: LFormula eb cs k c a l -> SFormula eb cs a
lToS = SF . fmap (const ())

-- fromNF :: NeutralFormula eb cs a l -> SFormula eb cs a
-- fromNF (NF f) = fromLFormula f

srchAxToSax :: SrchAxiom cs a l -> SAxiom cs a
srchAxToSax = SA . fmap (const ()) . unSrchAx

-- sAxiomIsSFormula
--   :: ElemBase eb a
--   => SAxiom cs a -> SFormula eb cs a
-- sAxiomIsSFormula = fromLFormula . axiomIsFormula . unSA

fromSrch :: SrchFormula eb cty a l k -> SFormula eb cty a
fromSrch (Srch f) = SF (fmap (const ()) f)

fromBasicNS
  :: NE.NonEmpty (BFormula a l)
  -> cty
  -> BFormula a l
  -> SAxiom cty a
fromBasicNS lc cs concl = case concl of
    BF f -> sAx fromF (BF (fmap (const ()) f)) cs
  where
    fromF = foldr1 bsConj (fmap (fmap (const ())) lc)

--------------------------------------------------------------------------------
-- Sequents.

data Sequent eb cty a =
  SQ (UnrestrCtxt (SAxiom cty a))
     (NonEmptyLinearCtxt (SFormula eb cty a))
     (SFormula eb cty a)
--  deriving Show

neutralize
  :: forall m l a cty eb.
     (PickMonad m l, Ord a, Ord l, Ord eb, Ord cty, Monoid cty)
  => Sequent eb cty a -> m (LGoalNSequent eb cty a l)
neutralize (SQ unrestr linear (SF concl)) =
  GNS <$> unrestrLabelled <*> linearNeutral <*> nGoal
  where
    unrestrLabelled =
      fmap fromFoldable . mapM pickLabelAx . asFoldable toList $ unrestr
    linearNeutral =
      fmap (fromNEList . join) . mapM neutralizeFormula . toNEList $
      linear
    nGoal = opaque <$> pickLabel concl

pickLabel
  :: PickMonad m l
  => LFormula eb cty k c a () -> m (SrchFormula eb cty a l k)
pickLabel = fmap Srch . traverse (const pick)

pickLabelAx :: PickMonad m l => SAxiom cty a -> m (SrchAxiom cty a l)
pickLabelAx = fmap SrchAx . traverse (const pick) . unSA

labelSF :: (PickMonad m l) => SFormula eb cty a -> m (SrchOpaque eb cty a l)
labelSF (SF f) = fmap (opaque . Srch) . traverse (const pick) $ f

data Tri a b c = T1 a | T2 b | T3 c

partitionNEEithers
  :: NE.NonEmpty (Either a b)
  -> Tri (NE.NonEmpty a) (NE.NonEmpty b) (NE.NonEmpty a, NE.NonEmpty b)
partitionNEEithers ((Left a) NE.:| xs) =
  case T.partitionEithers xs of
    (as,[]) -> T1 (a NE.:| as)
    (as,(b:bs)) -> T3 (a NE.:| as, b NE.:| bs)
partitionNEEithers ((Right b) NE.:| xs) =
  case T.partitionEithers xs of
    ([], bs) -> T2 (b NE.:| bs)
    ((a:as),bs) -> T3 (a NE.:| as, b NE.:| bs)

neutralizeOs
  :: (Ord a, Ord l)
  => NE.NonEmpty (SrchOpaque eb cty a l) -> NE.NonEmpty (SrchNeutral eb cty a l)
neutralizeOs opaques = case partitionNEEithers (fmap maybeNeutral opaques) of
  T1 neutrals -> neutrals
  T2 opaques -> neutralizeOs (join opaques)
  T3 (neutrals,opaques) -> neutrals <> neutralizeOs (join opaques)

neutralizeFormula
  :: (PickMonad m l, Ord a, Ord l)
  => SFormula eb cty a -> m (NE.NonEmpty (SrchNeutral eb cty a l))
neutralizeFormula = labelSF >>> fmap (return >>> neutralizeOs)
