{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}

module SFormula
  ( Sequent
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

instance Pretty (SFormula eb cty a) where
  pretty f = error "not implemented: SFormula.pretty"

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

laxToSax :: LAxiom cs a l -> SAxiom cs a
laxToSax = SA . fmap (const ())

-- sAxiomIsSFormula
--   :: ElemBase eb a
--   => SAxiom cs a -> SFormula eb cs a
-- sAxiomIsSFormula = fromLFormula . axiomIsFormula . unSA

fromSrch :: SrchFormula eb cty a l k -> SFormula eb cty a
fromSrch (Srch f) = SF (fmap (const ()) f)

fromBasicNS
  :: NE.NonEmpty (BioFormula a)
  -> cty
  -> BFormula a l
  -> SAxiom cty a
fromBasicNS lc cs concl = case concl of
    BF f -> sAx fromF (BF (fmap (const ()) f)) cs
  where
    fromF = foldr1 bsConj (fmap bsAtom lc)

--------------------------------------------------------------------------------
-- Sequents.

data Sequent eb cty a =
  SQ (UnrestrCtxt (SAxiom cty a))
     (LinearCtxt (SFormula eb cty a))
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
      fmap (fromFoldable . join) . mapM neutralizeFormula . asFoldable toList $
      linear
    nGoal = opaque <$> pickLabel concl

pickLabel :: PickMonad m l => LFormula eb cty k c a () ->
  m (SrchFormula eb cty a l k)
pickLabel = undefined -- traverse (const pick) concl

pickLabelAx :: PickMonad m l => SAxiom cty a -> m (SrchAxiom cty a l)
pickLabelAx = undefined -- traverse (const picK) . unSA

labelSF :: (PickMonad m l) => SFormula eb cty a -> m (SrchOpaque eb cty a l)
labelSF (SF f) = fmap (opaque . Srch) . traverse (const pick) $ f

neutralizeOs
  :: (Ord a, Ord l)
  => [SrchOpaque eb cty a l] -> [SrchNeutral eb cty a l]
neutralizeOs [] = []
neutralizeOs list =
  uncurry (++) . bimap id (neutralizeOs . join)
  . T.partitionEithers . fmap maybeNeutral $ list

neutralizeFormula
  :: (PickMonad m l, Ord a, Ord l)
  => SFormula eb cty a -> m [SrchNeutral eb cty a l]
neutralizeFormula = labelSF >>> fmap (return >>> neutralizeOs)
