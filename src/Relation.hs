{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

{-| Module of derived rule relations. -}

module Relation
  ( positiveFocal
  , positiveFocalDispatch
  , negativeFocalDispatch
  , MatchResult(..)
  , GoalResult(..)
  , filterPartitionRel
  ) where

import Data.Monoid
import Control.Applicative
import Prelude hiding (fail)
import Control.Monad.Fail
import Formula
import LabelledSequent
import Control.Monad hiding (fail)
import Rel

{-| Type of relations.

    A relation is an unbounded curried function of labelled sequents.  It is
    parameterized by the type of labels and biological atoms of the input
    labelled sequents, and by the codomain type of the relation. -}
type Relation l a b = Rel (LabelledSequent l a) b

--------------------------------------------------------------------------------
-- Sequent schemas.

-- | Type of unrestricted contexts which appear in sequent schemas.
newtype SchemaUCtxt l a = SUC (UnrestrCtxt l a)

-- | Type of linear contexts which appear in sequent schemas.
newtype SchemaLCtxt l a = SLC (LinearCtxt l a)

{-| Matches an unrestricted context against a schema.
    Returns the result in a MonadFail instance, which signals the error in case
    the match fails. -}
matchUnrestrCtxt
  :: (MonadFail m)
  => SchemaUCtxt l a -> UnrestrCtxt l a -> m (UnrestrCtxt l a)
matchUnrestrCtxt (SUC suc) uc = undefined

{-| Matches a linear context against a schema.
    Returns the result in a MonadFail instance, which signals the error in case
    the match fails. -}
matchLinearCtxt
  :: (MonadFail m)
  => SchemaLCtxt l a -> LinearCtxt l a -> m (LinearCtxt l a)
matchLinearCtxt (SLC slc) lc = undefined

--------------------------------------------------------------------------------
-- Act relations.

{-| Type indicating the possible shapes of an active relation.

    An active relations has the form

      act(gamma ; delta ; omega ==> xi)[...] -> gamma' ; delta' -->> res

    where either
    1. xi is a formula and res is empty, or
    2. xi is empty and res is a formula.
    -}
data ActCase = FullXiEmptyResult | EmptyXiFullResult

{-| Type of act schema goals.

    A schema goal can either be a label against which the input sequent is
    matched, or empty, in which case the match is always successful. -}
data SchemaGoal :: ActCase -> * -> * -> * where
  LabelGoal :: Label l a -> SchemaGoal FullXiEmptyResult l a
  EmptyGoal :: SchemaGoal EmptyXiFullResult l a

{-| Type of act schemas.

    An act schema is the propositional part of an act relation, where the omega
    part is empty. It is composed of an unrestricted context, a linear context,
    and a schema goal. -}
data SequentSchema actcase l a =
  Sch (UnrestrCtxt l a)
      (LinearCtxt l a)
      (SchemaGoal actcase l a)

{-| Type of goal results of an act relation.

    Such result is either a label of a formula, in which case the xi part of the
    corresponding act relation is empty, or it is empty, in which case the xi
    part of the corresponding act relation is a label of a formula. -}
data GoalResult :: ActCase -> * -> * -> * where
  LabelResult :: Label l a -> GoalResult EmptyXiFullResult l a
  EmptyResult :: GoalResult FullXiEmptyResult l a

{-| Type of the goal part of an act scheme.

    It can either be a formula label or empty. -}
data Xi :: ActCase -> Pole -> * -> * -> * where
  FullXi :: LFormula p l a -> Xi FullXiEmptyResult p l a
  EmptyXi :: Xi EmptyXiFullResult p l a

{-| Type of act relations match results.

    It is composed of an unrestricted context, a linear context, and a goal
    result parameterized, among others, by an ActCase. -}
data MatchResult actcase l a =
  MRes (UnrestrCtxt l a)
       (LinearCtxt l a)
       (GoalResult actcase l a)

{-| Matches a labelled sequent against an act sequent schema.
    Returns the result in a MonadFail instance, which signals the error in case
    the match fails. -}
match
  :: (Eq a, Eq l, MonadFail m, Alternative m)
  => SequentSchema c l a -> LabelledSequent l a -> m (MatchResult c l a)
match (Sch gamma delta schGoal) (LS gamma' delta' goal) = do
  gamma'' <- matchUnrestrCtxt (SUC gamma) gamma'
  delta'' <- matchLinearCtxt (SLC delta) delta'
  case schGoal of
    LabelGoal l ->
      guard (l == goal) >> (return $ MRes gamma'' delta'' EmptyResult)
    EmptyGoal -> return $ MRes gamma'' delta'' (LabelResult goal)

{-| Type of negative focused match results.

    Negative focus relations always return a result sequent with non-empty
    goal, so we explicitly indicate it in the type. The outcome is that result
    sequents with empty goals are statically rejected as ill-typed. -}
type NFocMatchResult l a = MatchResult EmptyXiFullResult l a

-- {-| Dispatching of negative synchronous formulas. Notice the type that enforces
--     input formulas to be both left synchronous and non-atomic. -}
-- negativeFocal
--   :: (Eq a, Eq l)
--   => LFormula LSRA l a -> Relation l a (NFocMatchResult l a)
-- negativeFocal = negativeFocalDispatch

{-| Negative focal relation.
    The fact that it returns a result sequent with non-empty goal is statically
    enforced by the type of the function. -}
negativeFocalDispatch
  :: forall p l a.
     (Eq a, Eq l, Ord a, Ord l)
  => LFormula p l a -> Relation l a (NFocMatchResult l a)
negativeFocalDispatch formula =
  case formula of
    FAtom (RBAtom a) ->
      return (MRes mempty mempty (LabelResult (A a)))
    FAtom (LBAtom _) -> fail "not right-biased"
    FConj _ _ _ ->
      leftActive
        mempty
        [OF formula]
        (EmptyXi :: Xi EmptyXiFullResult p l a)
    FImpl f1 f2 _ -> do
      (MRes gamma1 delta1 xi) <- negativeFocalDispatch f2
      (MRes gamma2 delta2 EmptyResult) <- positiveFocalDispatch f1
      return $
        MRes (gamma1 <> gamma2) (delta1 <> delta2) xi

type PFocMatchResult l a = MatchResult FullXiEmptyResult l a

{-| Type of positive focused match results.

    Positive focus relations always return a result sequent with empty
    goal, so we explicitly indicate it in the type. The outcome is that result
    sequents with non-empty goals are statically rejected as ill-typed. -}
positiveFocal
  :: (Eq a, Eq l, Ord l, Ord a)
  => LFormula LARS l a -> Relation l a (PFocMatchResult l a)
positiveFocal = positiveFocalDispatch

{-| Positive focal relation.
    The fact that it returns a result sequent with empty goal is statically
    enforced by the type of the function. -}
positiveFocalDispatch
  :: (Eq a, Eq l, Ord l, Ord a)
  => LFormula p l a -> Relation l a (PFocMatchResult l a)
positiveFocalDispatch formula =
  case formula of
    FAtom (LBAtom a) ->
      return (MRes mempty (singletonLinearCtxt (A a)) EmptyResult)
    FAtom (RBAtom _) -> fail "not left-biased"
    FImpl _ _ _ -> rightActive mempty [] formula
    FConj f1 f2 _ -> do
      (MRes gamma1 delta1 _) <- positiveFocalDispatch f1
      (MRes gamma2 delta2 _) <- positiveFocalDispatch f2
      return
        (MRes
           (gamma1 <> gamma2)
           (delta1 <> delta2)
           EmptyResult)

-- | Formulas with arbitrary polarity.
data OpaqueFormula l a = forall p . OF (LFormula p l a)

{-| Right active relation, that is active relation of the form

      act( ; delta ; omega ===> C)

    where xi is C, hence a formula (and of course non-empty).

    Notice how the type enforces that, xi being a formula and therefore
    non-empty, the result sequent will have an empty goal. -}
rightActive
  :: (Eq a, Eq l, Ord l, Ord a)
  => (LinearCtxt l a)
  -> [OpaqueFormula l a]
  -> LFormula p l a
  -> Relation l a (MatchResult FullXiEmptyResult l a)
rightActive delta omega formula =
  case formula of
    FAtom atom -> leftActive delta omega (FullXi formula)
    FConj f1 f2 _ -> leftActive delta omega (FullXi formula)
    FImpl f1 f2 _ -> rightActive delta ((OF f1) : omega) f2

{-| Left active relation, that is active relation of the form

      act( ; delta ; omega ===> Q)

    where xi is Q, hence a right-synchronous formula (and of course
    non-empty).

    Notice how the typeclass context enforces that the input formula is indeed
    right-synchronous. -}
leftActive
  :: (IsRightSynchronous p, Eq a, Eq l, Ord l, Ord a)
  => (LinearCtxt l a)
  -> [OpaqueFormula l a]
  -> Xi actcase p l a
  -> Relation l a (MatchResult actcase l a)
leftActive delta omega formula =
  case omega of
    [] -> matchRel delta formula
    (OF (FConj f1 f2 _):rest) -> leftActive delta (OF f2 : OF f1 : rest) formula
    (OF (FImpl _ _ l):rest) ->
      leftActive (addToLinCtxt (L l) delta) rest formula
    (OF (FAtom (LBAtom a)):rest) ->
      leftActive (addToLinCtxt (A a) delta) rest formula
    (OF (FAtom (RBAtom a)):rest) ->
      leftActive (addToLinCtxt (A a) delta) rest formula

{-| Active match relation.
    It requires the input xi formula (if any) to be right-synchronous (otherwise
    we would have a right active relation). -}
matchRel
  :: (IsRightSynchronous p, Eq a, Eq l, Ord l, Ord a)
  => (LinearCtxt l a)
  -> Xi actcase p l a
  -> Relation l a (MatchResult actcase l a)
matchRel delta xi = liftFun $ \inputSeq -> match schema inputSeq
  where
    schema = Sch mempty delta goal
    goal =
      case xi of
        EmptyXi -> EmptyGoal
        FullXi f -> LabelGoal (label f)
