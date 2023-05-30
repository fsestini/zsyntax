{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors -Wno-orphans -Wno-unused-imports #-}

module Zsyntax.Labelled.Rule.Interface where

import Otter (Subsumable(..))
import Data.Foldable (toList)
import Data.List (intersperse)
import Data.Set (Set, (\\), isSubsetOf)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M (lookup)
import Zsyntax.Labelled.Formula
import Data.Constraint (Dict(..))
import Data.MultiSet (MultiSet)
import Data.Function (on)
import Data.Kind (Type)

-- import Core.FormulaKind
-- import Formula
-- import LinearContext

--------------------------------------------------------------------------------
-- Neutral sequents

-- -- | Type of unrestricted contexts. Unrestricted contexts are made out of
-- -- elements of some type of axiomatic formulas.
-- type UCtxt = Set Ax
-- -- | Type of linear contexts. Linear contexts are made out of neutral formulas.
-- type LCtxt = LinearCtxt -- (Neutral Frml)

-- data NSequent' cty = NS
--   { _nsUC :: UCtxt
--   , _nsLC :: LCtxt
--   , _nsCty :: cty
--   , _nsConcl :: Opaque Frml
--   } deriving (Functor)

-- type NSequent = NSequent' Cty

-- prettyNS :: NSequent -> String
-- prettyNS (NS _ lc _ c) =
--   concat (intersperse "," (fmap (withNeutral prettyF) (lcList lc))) ++ " ==> " ++
--   withOpaque prettyF c

-- deriving instance Eq cty => Eq (NSequent' cty)
-- deriving instance Ord cty => Ord (NSequent' cty)

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
  , lsConcl :: Opaque a l
  }

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

-- | Predicate identifying those formula kinds corresponding to neutral
-- formulas.
class NeutralKind (k :: FKind) where
  decideNeutral :: Either (Dict (k ~ KAtom)) (Dict (k ~ KImpl))
instance NeutralKind KAtom where decideNeutral = Left Dict
instance NeutralKind KImpl where decideNeutral = Right Dict

-- | Type of neutral formulas, i.e. all formulas whose formula kind is
-- classified as neutral by 'NeutralKind'.
data Neutral a l = forall k . NeutralKind k => N (LFormula k a l)

deriving instance (Show a, Show l) => Show (Neutral a l)

withMaybeNeutral
  :: LFormula k a l
  -> (NeutralKind k => b)
  -> (LFormula KConj a l -> b)
  -> b
withMaybeNeutral fr f g = case fr of
  Atom {} -> f
  Impl {} -> f
  Conj {} -> g fr

withNeutral :: (forall k. NeutralKind k => LFormula k a l -> b) -> Neutral a l -> b
withNeutral f (N fr) = f fr

switchN :: (LFormula KAtom a l -> b) -> (LFormula KImpl a l -> b) -> Neutral a l -> b
switchN f g (N (x :: LFormula k a l)) =
  either (\Dict -> f x) (\Dict -> g x) (decideNeutral @k)

-- class Show1 (fr :: k -> *) where show1 :: fr a -> String
-- instance Show (Opaque a l) where show (O f) = "O " ++ show1 f
-- instance Show (Neutral a l) where show (N f) = "N " ++ show1 f

instance (Eq l, Eq a) => Eq (Neutral a l) where
  N f1 == N f2 = frmlHetEq f1 f2

instance (Ord l, Ord a) => Ord (Neutral a l) where
  compare (N f1) (N f2) = frmlHetOrd f1 f2

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
    -> Opaque a l
    -> SSchema a l FullXiEmptyResult

-- | Pre-sequents to be used as match results.
data MatchRes :: Type -> Type -> ActCase -> Type where
  MREmptyGoal :: UCtxt a l -> LCtxt a l -> MatchRes a l FullXiEmptyResult
  MRFullGoal
    :: UCtxt a l -> LCtxt a l -> ReactionList a -> Opaque a l
    -> MatchRes a l EmptyXiFullResult

data ZetaXi :: Type -> Type -> ActCase -> Type where
  FullZetaXi
    :: ReactionList a
    -> Opaque a l
    -> ZetaXi a l FullXiEmptyResult
  EmptyZetaXi :: ZetaXi a l EmptyXiFullResult

--------------------------------------------------------------------------------
-- Elementary bases and control sets

elemBaseAll :: (Foldable f, Ord a) => f (Opaque a l) -> ElemBase a
elemBaseAll = mconcat . fmap (withOpaque elemBase) . toList
  
lcBase :: Ord a => LCtxt a l -> ElemBase a
lcBase = foldMap (withNeutral elemBase)
