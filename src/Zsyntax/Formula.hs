{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Zsyntax.Formula where
  -- (
  --   -- * Biochemical formulas
  --   BioFormula(..)
  -- , ppBioFormula
  -- -- * Logical formulas
  -- , Axiom
  -- , axiom
  -- , axiom'
  -- , axForget
  -- , Formula
  -- , atom
  -- , conj
  -- , impl
  -- , ppFormula
  -- -- * Sequents
  -- , Sequent(..)
  -- , neutralize
  -- ) where

import Control.Arrow ((>>>))
import Data.Bifunctor (second)
import Zsyntax.Labelled.Formula
import Zsyntax.Labelled.Rule (Neutral(..),GoalNSequent(..))
-- import Data.MultiSet.NonEmpty
import Data.MultiSet (MultiSet, fromList)
import Data.Foldable (toList)
import Data.Set (Set)
import qualified Data.Set as S (fromList)
import Data.List.NonEmpty (NonEmpty(..), sort)
import Control.Monad.State
import Data.Either (partitionEithers)
import Data.Function (on)

--------------------------------------------------------------------------------
-- Biochemical atomic formulas

{-| Type of biochemical (non-logical) formulas, which constitute
    the logical atoms of logical formulas of Zsyntax.
    It is parameterized over the type of biochemical atoms. -}
data BioFormula a = BioAtom a
                  | BioInter (BioFormula a) (BioFormula a)
                  deriving (Functor, Foldable, Traversable, Show)

instance Semigroup (BioFormula a) where
  (<>) = BioInter

normalize :: Ord a => BioFormula a -> NonEmpty a
normalize (BioAtom x) = x :| []
normalize (BioInter f1 f2) = sort (normalize f1 <> normalize f2)

-- | Custom equality instance for biological atoms.
-- It includes commutativity of the biological interaction operator.
instance Ord a => Eq (BioFormula a) where
  (==) = on (==) normalize

instance Ord a => Ord (BioFormula a) where
  compare = on compare normalize

-- | Pretty-prints biochemical formulas, given a way to pretty print its atoms.
--
-- @
-- >>> ppBioFormula id (BioAtom "foo" <> BioAtom "bar" <> BioAtom "baz")
-- "((foo ⊙ bar) ⊙ baz)"
-- @
ppBioFormula :: (a -> String) -> BioFormula a -> String
ppBioFormula p (BioAtom x) = p x
ppBioFormula p (BioInter x y) =
  "(" ++ ppBioFormula p x ++ " ⊙ " ++ ppBioFormula p y ++ ")"

--------------------------------------------------------------------------------
-- Simple formulas

-- | Type of logical axioms of Zsyntax.
newtype Axiom a = Axiom { unSA :: LAxiom a () }
  deriving Show

axForget :: LAxiom a l -> Axiom a
axForget = Axiom . void

-- | Constructs an axiom from non-empty lists of logical atoms as premise and
-- conclusion.
axiom :: NonEmpty a -> ReactionList a -> NonEmpty a -> Axiom a
axiom prms cty concl = axiom' (f prms) cty (f concl)
  where f = foldl1 (bConj ()) . fmap BAtom

axiom' :: BFormula a () -> ReactionList a -> BFormula a () -> Axiom a
axiom' b1 r b2 = Axiom (LAx b1 r b2 ())

-- | Type of logical formulas of Zsyntax, parameterized by the type of atoms
-- (which are typically 'BioFormula's).
data Formula a = forall k . Formula (LFormula k a ())

-- | Pretty-prints Zsyntax formulas, given a way to pretty-print its atoms.
ppFormula :: (a -> String) -> Formula a -> String
ppFormula p (Formula f) = ppLFormula p f
-- TODO: wut?
-- @
-- >>> ppFormula id (impl (conj (atom "foo") (atom "bar")) mempty mempty (atom "baz"))
-- "(foo \8855 bar \8594 baz)"
-- @

deriving instance Show a => Show (Formula a)

instance Ord a => Eq (Formula a) where
  (Formula f1) == (Formula f2) = deepHetComp f1 f2 == EQ

instance Ord a => Ord (Formula a) where
  compare (Formula f1) (Formula f2) = deepHetComp f1 f2

instance Ord a => Eq (Axiom a) where
  (Axiom ax1) == (Axiom ax2) = deepHetComp (axToFormula ax1) (axToFormula ax2) == EQ

instance Ord a => Ord (Axiom a) where
  compare (Axiom ax1) (Axiom ax2) = deepHetComp (axToFormula ax1) (axToFormula ax2)

-- | Constructs an atomic formula from a logical atom.
atom :: a -> Formula a
atom = Formula . Atom

lToS :: LFormula k a l -> Formula a
lToS = Formula . void

-- | Constructs the conjunction of two formulas.
conj :: Formula a -> Formula a -> Formula a
conj (Formula f1) (Formula f2) = lToS (Conj f1 f2 ())

-- | Constructs a Zsyntax conditional (aka linear implication) between two
-- formulas, whose associated biochemical reaction is described by a given
-- elementary base and reaction list.
impl :: Formula a -> ElemBase a -> ReactionList a -> Formula a -> Formula a
impl (Formula f1) eb cs (Formula f2) = Formula (Impl f1 eb cs f2 ())

--------------------------------------------------------------------------------
-- Sequents

-- | Type of ZBS sequents.
data Sequent a =
  SQ { _sqUC    :: Set (Axiom a)
     , _sqLC    :: MultiSet (Formula a)
     , _sqConcl :: (Formula a)
     }
  deriving Show

nuLabel :: (Enum l, MonadState l m) => m l
nuLabel = do { s <- get ; put (succ s) ; return s }

-- | Turns a sequent into a labelled goal sequent.
neutralize
  :: (MonadState l m, Enum l, Ord a, Ord l)
  => Sequent a -> m (GoalNSequent a l)
neutralize (SQ unrestr linear (Formula concl)) = GNS <$> ul <*> ln <*> nGoal
  where
    ul = fmap S.fromList . mapM (traverse (const nuLabel) . unSA)
       . toList $ unrestr
    ln = fmap (fromList . join) . mapM neutralizeFormula . toList $ linear
    nGoal = O <$> traverse (const nuLabel) concl

maybeNeutral :: Opaque a l -> Either (Neutral a l) [Opaque a l]
maybeNeutral (O f@(Atom _)) = Left (N f)
maybeNeutral (O (Conj a b _)) = Right [O a, O b]
maybeNeutral (O f@Impl{}) = Left (N f)

neutralizeOs :: (Ord a, Ord l) => [Opaque a l] -> [Neutral a l]
neutralizeOs [] = []
neutralizeOs xs =
  uncurry (<>) . second (neutralizeOs . join) .
    partitionEithers . fmap maybeNeutral $ xs

neutralizeFormula
  :: (MonadState l m, Enum l, Ord a, Ord l) => Formula a -> m [Neutral a l]
neutralizeFormula = labelSF >>> fmap (return >>> neutralizeOs)
  where labelSF (Formula f) = fmap O . traverse (const nuLabel) $ f
