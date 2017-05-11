{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}

module SFormula
  ( SFormula(..)
  , SAxiom(..)
  , Sequent(..)
  , sAtom
  , sConj
  , sImpl
  , neutralize
  , sAxiomIsSFormula
  , fromLFormula
  , fromLAxiom
  , BioFormula(..)
  , LFormula(..)
  , pattern Impl
  , OLFormula(..)
  , ElemBase(..)
  , ControlSet(..)
  , ImplFormula(..)
  , sAx
  ) where

import RelFormula
import TypeClasses (PickMonad(..))
import Control.Monad
import qualified Data.Set as S
import UnrestrContext
import LinearContext
import Context
import Data.Foldable

--------------------------------------------------------------------------------

-- Simple formulas
newtype SFormula eb cs a = SF (OLFormula eb cs a ())
newtype NSFormula eb cs a = NSF
  { unNSF :: (NeutralFormula eb cs a ())
  } deriving (Show)
newtype SAxiom eb cs a = SA {unSA :: (Axiom eb cs a ())}

sAx :: SFormula eb cs a -> SFormula eb cs a -> cs a -> SAxiom eb cs a
sAx (SF (OLF f1)) (SF (OLF f2)) cs = SA (ImplF f1 EmptySpot cs f2 ())

instance Show a => Show (SFormula eb cs a) where
  show (SF (OLF f)) = deepShowFormula f

instance Show a => Show (SAxiom eb cs a) where
  show (SA ax) = deepShowImpl ax

instance (Ord a, Ord (eb a), Ord (cs a)) =>
         Eq (SFormula eb cs a) where
  (SF (OLF f1)) == (SF (OLF f2)) = deepHetCompare f1 f2 == EQ

instance (Ord a, Ord (eb a), Ord (cs a)) =>
         Ord (SFormula eb cs a) where
  compare (SF (OLF f1)) (SF (OLF f2)) = deepHetCompare f1 f2

instance (Ord a, Ord (eb a), Ord (cs a)) => Eq (SAxiom eb cs a) where
  (SA ax1) == (SA ax2) = compare ax1 ax2 == EQ

instance (Ord a, Ord (eb a), Ord (cs a)) => Ord (SAxiom eb cs a) where
  compare (SA ax1) (SA ax2) = deepImplCompare ax1 ax2

sAtom :: BioFormula a -> SFormula eb cs a
sAtom = SF . OLF . Atom

sConj :: SFormula eb cs a -> SFormula eb cs a -> SFormula eb cs a
sConj (SF (OLF f1)) (SF (OLF f2)) = SF (OLF (Conj f1 f2 ()))

sImpl :: SFormula eb cs a
      -> eb a
      -> cs a
      -> SFormula eb cs a
      -> SFormula eb cs a
sImpl (SF (OLF f1)) eb cs (SF (OLF f2)) = SF (OLF (Impl f1 eb cs f2 ()))

fromLFormula
  :: LFormula eb cs k a l -> SFormula eb cs a
fromLFormula = SF . OLF . fmap (const ())

fromLAxiom :: Axiom eb cs a l -> SAxiom eb cs a
fromLAxiom = SA . fmap (const ())

sAxiomIsSFormula
  :: ElemBase eb a
  => SAxiom eb cs a -> SFormula eb cs a
sAxiomIsSFormula (SA a) = SF . OLF $ (axiomIsFormula a)

--------------------------------------------------------------------------------
-- Sequents.

data Sequent eb cs a =
  SQ (UnrestrCtxt (SAxiom eb cs a))
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
        ((traverse (const pick) . unSA) :: SAxiom eb cs a -> m (Axiom eb cs a l)) $
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
neutralizeFormula (SF (OLF f@(Impl' _))) = [NSF (NF f)]
