{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
import Zsyntax.Labelled.Rule (Neutral, GoalNSequent(..))
import Data.MultiSet (MultiSet, fromList)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Foldable (toList)
import Data.Set (Set)
import qualified Data.Set as S (fromList)
import Data.List.NonEmpty (NonEmpty(..), sort)
import Control.Monad.State
import Data.Either (partitionEithers)
import Data.Function (on)
import Data.Text (Text)
import Data.Bifunctor.Sum (Sum(..))
import Zsyntax.ReactionList (traverseSet, traverseMultiset)

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
newtype Formula a = Formula { unFormula :: LFormula a () }
  deriving Show

traverseFormula :: (Applicative f, Ord b) => (a -> f b) -> Formula a -> f (Formula b)
traverseFormula f (Formula x) = Formula <$> traverseAtoms f x

-- | Pretty-prints Zsyntax formulas, given a way to pretty-print its atoms.
ppFormula :: (a -> Text) -> Formula a -> Text
ppFormula p = ppLFormula p . unFormula
-- TODO: wut?
-- @
-- >>> ppFormula id (impl (conj (atom "foo") (atom "bar")) mempty mempty (atom "baz"))
-- "(foo \8855 bar \8594 baz)"
-- @

-- deriving instance Show a => Show (Formula a)

instance Ord a => Eq (Formula a) where
  (Formula f1) == (Formula f2) = deepHetComp f1 f2 == EQ

instance Ord a => Ord (Formula a) where
  compare (Formula f1) (Formula f2) = deepHetComp f1 f2

instance Ord a => Eq (Axiom a) where
  (Axiom ax1) == (Axiom ax2) =
    on deepHetComp (injImpl . axToFormula) ax1 ax2 == EQ
    -- deepHetComp (axToFormula ax1) (axToFormula ax2) == EQ

instance Ord a => Ord (Axiom a) where
  compare (Axiom ax1) (Axiom ax2) =
    on deepHetComp (injImpl . axToFormula) ax1 ax2

-- | Constructs an atomic formula from a logical atom.
atom :: a -> Formula a
atom = Formula . Atom

lToS :: LFormula a l -> Formula a
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
     , _sqConcl :: Formula a
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
    nGoal = traverse (const nuLabel) concl

neutralizeOs :: (Ord a, Ord l) => [LFormula a l] -> [Neutral a l]
neutralizeOs [] = []
neutralizeOs xs =
  uncurry (<>) . second (neutralizeOs . join) . partitionEithers . fmap maybeNeutral $ xs
  where maybeNeutral = foldLSum (Left . L2) (\(LConj a b _) -> Right [a, b]) (Left . R2)

neutralizeFormula
  :: (MonadState l m, Enum l, Ord a, Ord l) => Formula a -> m [Neutral a l]
neutralizeFormula = labelSF >>> fmap (return >>> neutralizeOs)
  where labelSF (Formula f) = traverse (const nuLabel) f

newtype IntAtom = IntAtom Int deriving (Num, Show, Eq, Ord)

countAtoms' :: Ord a => Sequent a -> State (Map a IntAtom, IntAtom) (Sequent IntAtom)
countAtoms' (SQ uc lc c) =
  SQ <$> traverseSet (fmap Axiom . traverseAxiom f . unSA) uc
     <*> traverseMultiset (traverseFormula f) lc
     <*> traverseFormula f c
  where
    f :: Ord a => a -> State (Map a IntAtom, IntAtom) IntAtom
    f a = get >>= \(m, n) -> case M.lookup a m of
      Just i -> pure i
      Nothing -> put (M.insert a n m, n + 1) >> pure n

countAtoms :: Ord a => Sequent a -> (Sequent IntAtom, Map a IntAtom)
countAtoms s = (s', m) where (s', (m, _)) = runState (countAtoms' s) (M.empty, 0)
