{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Zsyntax.Labelled.Rule.Interface where

import Otter (Subsumable(..))
import Data.Foldable (toList)
import Data.Set (Set, (\\), isSubsetOf)
import Zsyntax.Labelled.Formula
import Data.MultiSet (MultiSet)
import Data.Kind (Type)
import Data.Bifunctor.Sum (Sum (..))
import Zsyntax.ReactionList (traverseSet, traverseMultiset)
import Control.Monad.Identity (Identity(runIdentity, Identity))

--------------------------------------------------------------------------------
-- Labelled sequents

-- | Type of labelled unrestricted contexts, i.e. sets of labelled axioms.
type UCtxt a l = Set (LAxiom a l)

-- | Type of labelled neutral contexts, i.e. multisets of neutral labelled
-- formulas.
type LCtxt a l = MultiSet (Neutral a l)

-- | Type of labelled sequents.
data LSequent a l = LS
  { lsUCtxt :: UCtxt a l
  , lsLCtxt :: LCtxt a l
  , lsCty :: ReactionList a
  , lsConcl :: LFormula a l
  }
  deriving Show

traverseLSequent
  :: (Applicative f, Ord l, Ord b) => (a -> f b) -> LSequent a l -> f (LSequent b l)
traverseLSequent f (LS uc lc r c) =
  LS <$> traverseSet (traverseAxiom f) uc
     <*> traverseMultiset (traverseNeutral f) lc
     <*> traverseRL f r
     <*> traverseAtoms f c

mapLSequent :: (Ord l, Ord b) => (a -> b) -> LSequent a l -> LSequent b l
mapLSequent f = runIdentity . traverseLSequent (Identity . f)

data SubCtxt a = SC
  { _scOnOnlyFirst :: [a]
  , _scRestFirst :: [a]
  }

subCtxtOf :: Ord a => Set a -> Set a -> SubCtxt a
subCtxtOf s1 s2 =
  if isSubsetOf s1 s2 then SC [] (toList s1) else SC (toList df) df'
  where df = s1 \\ s2 ; df' = toList (s1 \\ df)

instance (Ord a, Ord l) => Subsumable (LSequent a l) where
  subsumes  (LS uc lc c fr) (LS uc' lc' c' fr') =
    fr == fr' && lc == lc' && c == c' && null (_scOnOnlyFirst (uc `subCtxtOf` uc'))

--------------------------------------------------------------------------------
-- Neutral formulas.

-- -- | Predicate identifying those formula kinds corresponding to neutral
-- -- formulas.
-- class NeutralKind (k :: FKind) where
--   decideNeutral :: Either (Dict (k ~ KAtom)) (Dict (k ~ KImpl))
-- instance NeutralKind KAtom where decideNeutral = Left Dict
-- instance NeutralKind KImpl where decideNeutral = Right Dict

-- | Type of neutral formulas, i.e. atoms and implications.
type Neutral = Sum LAtom LImpl
  -- a l = forall k . NeutralKind k => N (LFormula k a l)

-- deriving instance (Show a, Show l) => Show (Neutral a l)

traverseNeutral :: (Ord b, Applicative f) => (a -> f b) -> Neutral a l -> f (Neutral b l)
traverseNeutral f = \case
  L2 x -> L2 <$> traverseAtom f x
  R2 x -> R2 <$> traverseImpl f x

injNeutral :: Neutral a l -> LFormula a l
injNeutral = \case
  L2 a -> LFormula (L2 a)
  R2 i -> LFormula (R2 (R2 i))

-- withMaybeNeutral
--   :: LFormula k a l
--   -> (NeutralKind k => b)
--   -> (LFormula KConj a l -> b)
--   -> b
-- withMaybeNeutral fr f g = case fr of
--   Atom {} -> f
--   Impl {} -> f
--   Conj {} -> g fr

withMaybeNeutral :: LFormula a l -> (Neutral a l -> b) -> (LConj a l -> b) -> b
withMaybeNeutral (LFormula fr) f g = case fr of
  L2 a -> f (L2 a)
  R2 (L2 c) -> g c
  R2 (R2 i) -> f (R2 i)

withNeutral :: (LFormula a l -> b) -> Neutral a l -> b
withNeutral f = f . injNeutral

-- switchN :: (LFormula KAtom a l -> b) -> (LFormula KImpl a l -> b) -> Neutral a l -> b
-- switchN f g (N (x :: LFormula k a l)) =
--   either (\Dict -> f x) (\Dict -> g x) (decideNeutral @k)

-- instance (Eq l, Eq a) => Eq (Neutral a l) where
--   N f1 == N f2 = frmlHetEq f1 f2

-- instance (Ord l, Ord a) => Ord (Neutral a l) where
--   compare (N f1) (N f2) = frmlHetOrd f1 f2

--------------------------------------------------------------------------------

-- | Linear contexts that appear in sequent schemas.
newtype SchemaLCtxt a l = SLC (LCtxt a l)

deriving instance (Ord l, Ord a) => Semigroup (SchemaLCtxt a l)
-- deriving instance Monoid SchemaLCtxt

{-| Type indicating the possible shapes of an active relation.
    An active relation has the form

      act(delta ; omega ==>_zeta xi)[...] -> gamma' ; delta' -->> res

    where either
    1. xi is a formula, zeta is a control set, and res is empty, or
    2. xi is empty, zeta is empty, and res is a formula. -}
data ActCase = FullXiEmptyResult | EmptyXiFullResult

-- | Sequent schemas.
data SSchema :: Type -> Type -> ActCase -> Type where
  SSEmptyGoal :: SchemaLCtxt a l -> SSchema a l EmptyXiFullResult
  SSFullGoal
    :: SchemaLCtxt a l
    -> ReactionList a
    -> LFormula a l
    -> SSchema a l FullXiEmptyResult

-- | Pre-sequents to be used as match results.
data MatchRes :: Type -> Type -> ActCase -> Type where
  MREmptyGoal :: UCtxt a l -> LCtxt a l -> MatchRes a l FullXiEmptyResult
  MRFullGoal
    :: UCtxt a l -> LCtxt a l -> ReactionList a -> LFormula a l
    -> MatchRes a l EmptyXiFullResult

data ZetaXi :: Type -> Type -> ActCase -> Type where
  FullZetaXi
    :: ReactionList a
    -> LFormula a l
    -> ZetaXi a l FullXiEmptyResult
  EmptyZetaXi :: ZetaXi a l EmptyXiFullResult

--------------------------------------------------------------------------------
-- Elementary bases and control sets

elemBaseAll :: (Foldable f, Ord a) => f (LFormula a l) -> ElemBase a
elemBaseAll = mconcat . fmap elemBase . toList

lcBase :: Ord a => LCtxt a l -> ElemBase a
lcBase = foldMap (withNeutral elemBase)
