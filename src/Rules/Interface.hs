{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}

module Rules.Interface where

import Data.Constraint
import Rel
import LinearContext
import UnrestrContext
import Data.Foldable (toList, fold)

data FKind = KAtom | KConj | KImpl

data FKindCase k
  = AtomCase (Dict (k ~ KAtom))
  | ImplCase (Dict (k ~ KImpl))
  | ConjCase (Dict (k ~ KConj))

data ImplRepr (fr :: FKind -> *) eb cty payload =
  forall k2 k1. IR (fr k1) eb cty (fr k2) payload

data ConjRepr (fr :: FKind -> *) payload =
  forall k1 k2 . CR (fr k1) (fr k2) payload

data AtomRepr payload at = AR at payload

class (AtomClss frml, ConjClss frml, ImplClss frml) =>
      Formula (frml :: FKind -> *) where
  type Ax frml :: *
  cases :: frml k -> FKindCase k
  hetCompare :: frml k1 -> frml k2 -> Ordering

class AxiomClss (Ax frml) => HasAxiom (frml :: FKind -> *) where
  axIsFormula :: (Ax frml) -> frml KImpl
  -- sideIsFormula :: SideFrml (Ax frml) -> Opaque frml
  -- axCtyIsCty :: AxCty (Ax frml) -> Cty frml

class ImplClss (frml :: FKind -> *) where
  type ImplPayload frml :: *
  type Eb frml :: *
  type Cty frml :: *
  reprImpl :: frml KImpl -> ImplRepr frml (Eb frml) (Cty frml) (ImplPayload frml)
  impl :: frml k1 -> Eb frml -> Cty frml -> frml k2 -> ImplPayload frml -> frml KImpl

class ConjClss frml where
  type ConjPayload frml :: *
  reprConj :: frml KConj -> ConjRepr frml (ConjPayload frml)
  conj :: frml k1 -> frml k2 -> ConjPayload frml -> frml KConj

class AtomClss frml where
  type AtomPayload frml :: *
  type AtomType frml :: *
  reprAtom :: frml KAtom -> AtomRepr (AtomPayload frml) (AtomType frml)
  atom :: AtomPayload frml -> AtomType frml -> frml KAtom

data AxRepr fr cty pay =
  forall . AxR fr cty fr pay

class AxiomClss ax where
  type SideFrml ax :: *
  type AxPayload ax :: *
  type AxCty ax :: *
  reprAx :: ax -> AxRepr (SideFrml ax) (AxCty ax) (AxPayload ax)

class AxiomKind (k :: FKind) where
class NeutralKind (k :: FKind) where
  decideNeutral :: Either (Dict (k ~ KAtom)) (Dict (k ~ KImpl))
instance NeutralKind KAtom where
  decideNeutral = Left Dict
instance NeutralKind KImpl where
  decideNeutral = Right Dict

--------------------------------------------------------------------------------
-- View-pattern functions

switchN
  :: (Formula fr)
  => Neutral fr
  -> Either
       (AtomRepr (AtomPayload fr) (AtomType fr))
       (ImplRepr fr (Eb fr) (Cty fr) (ImplPayload fr))
switchN (N (formula :: fr k)) =
  case decideNeutral @k of
    Left Dict -> Left (reprAtom formula)
    Right Dict -> Right (reprImpl formula)

data Tri a b c = T1 a | T2 b | T3 c

class TriFunctor f where
  trimap :: (a -> a') -> (b -> b') -> (c -> c') -> f a b c -> f a' b' c'

instance TriFunctor Tri where
  trimap f g h (T1 x) = T1 (f x)
  trimap f g h (T2 x) = T2 (g x)
  trimap f g h (T3 x) = T3 (h x)

switchF :: (Formula fr) => fr k ->
  Tri (Dict (k ~ KAtom), AtomRepr (AtomPayload fr) (AtomType fr))
      (Dict (k ~ KConj), ConjRepr fr (ConjPayload fr))
      (Dict (k ~ KImpl), ImplRepr fr (Eb fr) (Cty fr) (ImplPayload fr))
switchF f = case cases f of
  AtomCase Dict -> T1 (Dict, reprAtom f)
  ConjCase Dict -> T2 (Dict, reprConj f)
  ImplCase Dict -> T3 (Dict, reprImpl f)

switchF' :: (Formula fr) => fr k ->
  Tri (AtomRepr (AtomPayload fr) (AtomType fr))
      (ConjRepr fr (ConjPayload fr))
      (ImplRepr fr (Eb fr) (Cty fr) (ImplPayload fr))
switchF' = trimap snd snd snd . switchF

--------------------------------------------------------------------------------
-- Opaque and neutral formulas.

data Opaque (frml :: FKind -> *) = forall k . O (frml k)
data Neutral (frml :: FKind -> *) = forall k . (NeutralKind k) => N (frml k)

opaque :: fr k -> Opaque fr
opaque = O

instance Formula (frml :: FKind -> *) => Eq (Opaque frml) where
  (O f1) == (O f2) = hetCompare f1 f2 == EQ

instance Formula (frml :: FKind -> *) => Ord (Opaque frml) where
  compare (O f1) (O f2) = hetCompare f1 f2

instance Formula (frml :: FKind -> *) => Eq (Neutral frml) where
  (N f1) == (N f2) = hetCompare f1 f2 == EQ

instance Formula (frml :: FKind -> *) => Ord (Neutral frml) where
  compare (N f1) (N f2) = hetCompare f1 f2

data NSequent axs frml cty =
  NS (UCtxt axs) (LCtxt frml) cty (Opaque frml)
  deriving (Eq, Ord)

-- | Type of derivation terms-decorated data.
data DT term payload = DT
  { term :: term
  , payload :: payload
  } deriving (Eq, Ord)

-- | Derivation term-decorated neutral sequents.
type DTSequent term axs frml cty = DT term (NSequent axs frml cty)

type Relation term axs frml cty b = Rel (DTSequent term axs frml cty) b

-- | Type of unrestricted contexts. Unrestricted contexts are made out of
-- elements of some type of axiomatic formulas.
type UCtxt axs = UnrestrCtxt axs
-- | Type of linear contexts. Linear contexts are made out of neutral formulas.
type LCtxt frml = LinearCtxt (Neutral frml)

-- | Linear contexts that appear in sequent schemas.
newtype SchemaLCtxt frml = SLC (LCtxt frml) deriving (Monoid)

{-| Type indicating the possible shapes of an active relation.
    An active relation has the form

      act(delta ; omega ==>_zeta xi)[...] -> gamma' ; delta' -->> res

    where either
    1. xi is a formula, zeta is a control set, and res is empty, or
    2. xi is empty, zeta is empty, and res is a formula. -}
data ActCase = FullXiEmptyResult | EmptyXiFullResult

-- | Sequent schemas.
data SSchema :: ActCase -> (FKind -> *) -> * -> * where
  SSEmptyGoal :: SchemaLCtxt fr -> SSchema EmptyXiFullResult fr cty
  SSFullGoal
    :: SchemaLCtxt fr
    -> cty
    -> Opaque fr
    -> SSchema FullXiEmptyResult fr cty

-- | Pre-sequents to be used as match results.
data MatchRes :: ActCase -> * -> (FKind -> *) -> * where
  MREmptyGoal :: UCtxt ax -> LCtxt fr -> MatchRes FullXiEmptyResult ax fr
  MRFullGoal
    :: UCtxt ax
    -> LCtxt fr
    -> Cty fr
    -> Opaque fr
    -> MatchRes EmptyXiFullResult ax fr

data ZetaXi :: ActCase -> (FKind -> *) -> * where
  FullZetaXi :: Cty frml -> Opaque frml -> ZetaXi FullXiEmptyResult frml
  EmptyZetaXi :: ZetaXi EmptyXiFullResult frml

--------------------------------------------------------------------------------
-- Elementary bases and control sets

class (Monoid (Eb frml), Eq (Eb frml), Ord (Eb frml), ImplClss frml) =>
      HasElemBase frml where
  formulaBase :: frml k -> Eb frml

-- | Typeclass of matched elementary bases and control types
class BaseCtrl eb cty where
  respects :: eb -> cty -> Bool

-- | Typeclass of control types
class (ImplClss frml, Monoid (Cty frml), Eq (Cty frml), Ord (Cty frml)) =>
      HasControlType frml where

type HasBaseCtrl frml =
  (HasElemBase frml, HasControlType frml, BaseCtrl (Eb frml) (Cty frml))

oFormulaBase :: HasElemBase frml => Opaque frml -> Eb frml
oFormulaBase (O f) = formulaBase f

elemBaseAll
  :: (HasElemBase frml, Foldable f)
  => f (Opaque frml) -> Eb frml
elemBaseAll = fold . map oFormulaBase . toList

--------------------------------------------------------------------------------
-- Derivation terms

class Formula frml => DerTerm term frml where
  init :: AtomType frml -> term
  copy :: term -> (Ax frml) -> term
  conjR :: term -> term -> frml KConj -> term
  conjL :: term -> frml KConj -> term
  implR :: term -> frml KImpl -> term
  implL :: term -> term -> frml KImpl -> term
