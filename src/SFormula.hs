{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}

module SFormula
  ( SFormula(..)
  , SAxiom(..)
  , Sequent(..)
  , sAtom
  , fromBasicNS
  , sConj
  , sImpl
  , neutralize
  , sAxiomIsSFormula
  , fromLFormula
  , fromLAxiom
  , BioFormula(..)
  , LFormula(..)
  , OLFormula(..)
  , ElemBase(..)
  , ControlSet(..)
  , bsAtom
  , bsConj
  , sAx
  , U(..)
  , pattern Impl
  ) where

import RelFormula
import TypeClasses (PickMonad(..))
import Control.Monad
import qualified Data.Set as S
import UnrestrContext
import LinearContext
import Context
import Data.Foldable
import qualified TypeClasses as T
import qualified Data.List.NonEmpty as NE

--------------------------------------------------------------------------------
-- Basic simple formulas

type BSFormula cs a = BFormula cs a ()
  --forall k . BSF (LFormula U cs k CBasic a ())
newtype SAxiom cs a = SA {unSA :: (LAxiom cs a ())}

bsAtom :: BioFormula a -> BSFormula cs a
bsAtom x = BF (Atom x)

bsConj :: BSFormula cs a -> BSFormula cs a -> BSFormula cs a
bsConj (BF f1) (BF f2) = BF (Conj f1 f2 ())

sAx :: BSFormula cs a -> BSFormula cs a -> cs a -> SAxiom cs a
sAx (BF f1) (BF f2) cs = SA (ImplF f1 U cs f2 ())

--------------------------------------------------------------------------------

-- Simple formulas
newtype SFormula eb cs a = SF (OLFormula eb cs a ())
newtype NSFormula eb cs a = NSF
  { unNSF :: (NeutralFormula eb cs a ())
  } deriving (Show)


-- sAx :: SFormula eb cs a -> SFormula eb cs a -> cs a -> SAxiom cs a
-- sAx (SF (OLF f1)) (SF (OLF f2)) cs = SA (ImplF f1 EmptySpot cs f2 ())

instance Show a => Show (SFormula eb cs a) where
  show (SF (OLF f)) = deepShowFormula f

deriving instance (Show a, Show (cs a)) => Show (SAxiom cs a)

-- instance Show a => Show (SAxiom cs a) where
--   show (SA ax) = deepShowImpl ax

instance (Ord a, Ord (eb a), Ord (cs a)) =>
         Eq (SFormula eb cs a) where
  (SF (OLF f1)) == (SF (OLF f2)) = deepHetCompare f1 f2 == EQ

instance (Ord a, Ord (eb a), Ord (cs a)) =>
         Ord (SFormula eb cs a) where
  compare (SF (OLF f1)) (SF (OLF f2)) = deepHetCompare f1 f2

instance (Ord a, Ord (cs a)) => Eq (SAxiom cs a) where
  (SA ax1) == (SA ax2) = compare ax1 ax2 == EQ

instance (Ord a, Ord (cs a)) =>
         Ord (SAxiom cs a) where
  compare (SA ax1) (SA ax2) = deepImplCompare ax1 ax2

sAtom :: BioFormula a -> SFormula eb cs a
sAtom = SF . OLF . Atom

sConj :: SFormula eb cs a -> SFormula eb cs a -> SFormula eb cs a
sConj (SF (OLF f1)) (SF (OLF f2)) =
  fromLFormula (Conj (liftComplexity f1) (liftComplexity f2) ())

sImpl :: SFormula eb cs a
      -> eb a
      -> cs a
      -> SFormula eb cs a
      -> SFormula eb cs a
sImpl (SF (OLF f1)) eb cs (SF (OLF f2)) =
  SF (OLF (Impl (liftComplexity f1) eb cs (liftComplexity f2) ()))

fromLFormula
  :: LFormula eb cs k c a l -> SFormula eb cs a
fromLFormula = SF . OLF . fmap (const ())

fromLAxiom :: LAxiom cs a l -> SAxiom cs a
fromLAxiom = SA . fmap (const ())

sAxiomIsSFormula
  :: ElemBase eb a
  => SAxiom cs a -> SFormula eb cs a
sAxiomIsSFormula = fromLFormula . axiomIsFormula . unSA

fromBasicNS
  :: NE.NonEmpty (BioFormula a)
  -> cs a
  -> BFormula cs a l
  -> SAxiom cs a
fromBasicNS lc cs concl = case concl of
    BF f -> sAx fromF (BF (fmap (const ()) f)) cs
  where
    fromF = foldr1 bsConj (fmap bsAtom lc)

--------------------------------------------------------------------------------
-- Sequents.

data Sequent eb cs a =
  SQ (UnrestrCtxt (SAxiom cs a))
     (LinearCtxt (SFormula eb cs a))
     (SFormula eb cs a)
  deriving Show

neutralize
  :: forall eb cs m l a . (PickMonad m l, Ord a, Ord l, Ord (eb a), Ord (cs a))
  => Sequent eb cs a -> Maybe (cs a) -> m (GoalNeutralSequent eb cs a l)
neutralize (SQ unrestr linear (SF (OLF concl))) goalCS =
  GNS <$> nUnrestr <*> nLinear <*> (return goalCS) <*> nGoal
  where
    nUnrestr =
      fmap fromFoldable $
      mapM
        ((traverse (const pick) . unSA) :: SAxiom cs a -> m (LAxiom cs a l)) $
      (asFoldable toList unrestr)
    nLinear =
      fmap fromFoldable $
      mapM
        ((traverse (const pick) . unNSF) :: NSFormula eb cs a -> m (NeutralFormula eb cs a l)) $
      (asFoldable (concatMap neutralizeFormula . toList) linear)
    nGoal = OLF <$> traverse (const pick) concl

neutralizeFormula :: SFormula eb cs a -> [NSFormula eb cs a]
neutralizeFormula (SF (OLF (Conj f1 f2 _))) =
  neutralizeFormula (SF (OLF f1)) ++ neutralizeFormula (SF (OLF f2))
neutralizeFormula (SF (OLF a@(Atom _))) = [NSF (NF a)]
neutralizeFormula (SF (OLF f@(Impl _ _ _ _ _))) = [NSF (NF f)]
