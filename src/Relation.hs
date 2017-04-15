{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Relation
  ( positiveFocal
  , positiveFocalDispatch
  , negativeFocalDispatch
  , MatchResult(..)
  , GoalResult(..)
  , filterPartitionRel
  ) where

import Formula
import qualified Data.Set as S
import Rel

type Relation l a b = Rel (LabelledSequent l a) b

data SchemaGoal :: ActCase -> * -> * -> * where
  LabelGoal :: Label l a -> SchemaGoal FullXiEmptyResult l a
  EmptyGoal :: SchemaGoal EmptyXiFullResult l a

data SequentSchema actcase l a =
  Sch (UnrestrCtxt l a)
      (LinearCtxt l a)
      (SchemaGoal actcase l a)

data ActCase = FullXiEmptyResult | EmptyXiFullResult
data GoalResult :: ActCase -> * -> * -> * where
  LabelResult :: Label l a -> GoalResult EmptyXiFullResult l a
  EmptyResult :: GoalResult FullXiEmptyResult l a

data Xi :: ActCase -> Pole -> * -> * -> * where
  FullXi :: LFormula p l a -> Xi FullXiEmptyResult p l a
  EmptyXi :: Xi EmptyXiFullResult p l a

data MatchResult actcase l a =
  MRes (UnrestrCtxt l a)
       (LinearCtxt l a)
       (GoalResult actcase l a)

match
  :: (Eq a, Eq l)
  => SequentSchema c l a -> LabelledSequent l a -> Maybe (MatchResult c l a)
match (Sch gamma delta schGoal) (LS gamma' delta' goal) = do
  gamma'' <- matchUnrestrCtxt (SUC gamma) gamma'
  delta'' <- matchLinearCtxt (SLC delta) delta'
  case schGoal of
    LabelGoal l ->
      guard (l == goal) >> (return $ MRes gamma'' delta'' EmptyResult)
    EmptyGoal -> return $ MRes gamma'' delta'' (LabelResult goal)


type NFocMatchResult l a = MatchResult EmptyXiFullResult l a

-- {-| Dispatching of negative synchronous formulas. Notice the type that enforces
--     input formulas to be both left synchronous and non-atomic. -}
-- negativeFocal
--   :: (Eq a, Eq l)
--   => LFormula LSRA l a -> Relation l a (NFocMatchResult l a)
-- negativeFocal = negativeFocalDispatch

negativeFocalDispatch
  :: forall p l a.
     (Eq a, Eq l)
  => LFormula p l a -> Relation l a (NFocMatchResult l a)
negativeFocalDispatch formula =
  case formula of
    FAtom (RBAtom a) ->
      return (MRes emptyUnrestrCtxt emptyLinearCtxt (LabelResult (A a)))
    FAtom (LBAtom _) -> fail "not right-biased"
    FConj _ _ _ ->
      leftActive
        emptyLinearCtxt
        [OF formula]
        (EmptyXi :: Xi EmptyXiFullResult p l a)
    FImpl f1 f2 _ -> do
      (MRes gamma1 delta1 xi) <- negativeFocalDispatch f2
      (MRes gamma2 delta2 EmptyResult) <- positiveFocalDispatch f1
      return $
        MRes (mergeUnrestrCtxt gamma1 gamma2) (mergeLinearCtxt delta1 delta2) xi

type PFocMatchResult l a = MatchResult FullXiEmptyResult l a

positiveFocal
  :: (Eq a, Eq l)
  => LFormula LARS l a -> Relation l a (PFocMatchResult l a)
positiveFocal = positiveFocalDispatch

positiveFocalDispatch
  :: (Eq a, Eq l)
  => LFormula p l a -> Relation l a (PFocMatchResult l a)
positiveFocalDispatch formula =
  case formula of
    FAtom (LBAtom a) ->
      return (MRes emptyUnrestrCtxt (singletonLinearCtxt (A a)) EmptyResult)
    FAtom (RBAtom _) -> fail "not left-biased"
    FImpl _ _ _ -> rightActive emptyLinearCtxt [] formula
    FConj f1 f2 _ -> do
      (MRes gamma1 delta1 _) <- positiveFocalDispatch f1
      (MRes gamma2 delta2 _) <- positiveFocalDispatch f2
      return
        (MRes
           (mergeUnrestrCtxt gamma1 gamma2)
           (mergeLinearCtxt delta1 delta2)
           EmptyResult)

data OpaqueFormula l a = forall p . OF (LFormula p l a)

rightActive
  :: (Eq a, Eq l)
  => (LinearCtxt l a)
  -> [OpaqueFormula l a]
  -> LFormula p l a
  -> Relation l a (MatchResult FullXiEmptyResult l a)
rightActive delta omega formula =
  case formula of
    FAtom atom -> leftActive delta omega (FullXi formula)
    FConj f1 f2 _ -> leftActive delta omega (FullXi formula)
    FImpl f1 f2 _ -> rightActive delta ((OF f1) : omega) f2

-- | Left active relations.
leftActive
  :: (IsRightSynchronous p, Eq a, Eq l)
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

-- | Match relation.
matchRel
  :: (IsRightSynchronous p, Eq a, Eq l)
  => (LinearCtxt l a)
  -> Xi actcase p l a
  -> Relation l a (MatchResult actcase l a)
matchRel delta xi = liftFun $ \inputSeq -> match schema inputSeq
  where
    schema = Sch (S.empty) delta goal
    goal =
      case xi of
        EmptyXi -> EmptyGoal
        FullXi f -> LabelGoal (label f)
