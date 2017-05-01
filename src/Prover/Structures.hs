{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Prover.Structures
  ( Stage(..)
  , SearchSequent
  , ActiveSequent
  , InactiveSequent
  , ActiveSequents
  , InactiveSequents
  , ConclSequent
  , GlobalIndex
  , Rule
  , RuleRes
  , applyRule
  , initialIsFSChecked
  , initialIsBSChecked
  , initialize
  , subsumesGoalOp
  , removeSubsumedByOp
  , fwdSubsumes
  , activate
  , popInactiveOp
  , addToInactives
  , addToIndex
  , foldActives
  , Prover.Structures.initialSequentsAndRules
  , isGoal
  , makeGoal
  , emptyActives
  , emptyInactives
  , emptyGlobalIndex
  ) where

import Data.Profunctor
import Control.Arrow
import Control.Monad.Fail
import qualified Data.Set as S
import Rel
import Relation (DLSequent)
import Prover.Frontier (initialSequentsAndRules)
import Formula
import ForwardSequent
import TypeClasses (Coercible(..))

--------------------------------------------------------------------------------
-- Types.

data Stage
  = Initial    -- | Initial sequent
  | Active     -- | Active sequent
  | Inactive   -- | Inactive sequent
  | Concl      -- | Conclusion sequent
  | FSChecked  -- | Forward subsumption-checked
  | BSChecked  -- | Backward subsumption-checked
  | GlIndex    -- | Global index sequent
  | Goal       -- | Goal sequent

data SearchSequent :: Stage -> * -> * where
  InitSS :: seq -> SearchSequent Initial seq
  ActiveSS :: seq -> SearchSequent Active seq
  InactiveSS :: seq -> SearchSequent Inactive seq
  ConclSS :: seq -> SearchSequent Concl seq
  FSCheckedSS :: seq -> SearchSequent FSChecked seq
  BSCheckedSS :: seq -> SearchSequent BSChecked seq
  GlIndexSS :: seq -> SearchSequent GlIndex seq
  GoalSS :: seq -> SearchSequent Goal seq

extractSequent :: SearchSequent s seq -> seq
extractSequent (InitSS s) = s
extractSequent (ActiveSS s) = s
extractSequent (InactiveSS s) = s
extractSequent (ConclSS s) = s
extractSequent (BSCheckedSS s) = s
extractSequent (FSCheckedSS s) = s
extractSequent (GlIndexSS s) = s
extractSequent (GoalSS s) = s

instance Eq seq => Eq (SearchSequent s seq) where
  s1 == s2 = (extractSequent s1) == (extractSequent s2)

instance Ord seq => Ord (SearchSequent s seq) where
  compare s1 s2 = compare (extractSequent s1) (extractSequent s2)

instance ForwardSequent seq => ForwardSequent (SearchSequent s seq) where
  subsumes s1 s2 = subsumes (extractSequent s1) (extractSequent s2)

type ActiveSequent seq = SearchSequent Active seq
newtype ActiveSequents seq = AS (S.Set (SearchSequent Active seq))
type InactiveSequent seq = SearchSequent Inactive seq
newtype InactiveSequents seq = IS (S.Set (InactiveSequent seq))
type ConclSequent seq = SearchSequent Concl seq
newtype GlobalIndex seq = GI (S.Set (SearchSequent GlIndex seq))

--------------------------------------------------------------------------------

initialize :: seqty -> SearchSequent Initial seqty
initialize = InitSS

initialIsFSChecked :: SearchSequent Initial seqty
                   -> SearchSequent FSChecked seqty
initialIsFSChecked (InitSS s) = FSCheckedSS s

initialIsBSChecked :: SearchSequent Initial seqty
                   -> SearchSequent BSChecked seqty
initialIsBSChecked (InitSS s) = BSCheckedSS s

makeGoal :: seqty -> SearchSequent Goal seqty
makeGoal = GoalSS

emptyActives :: Ord seq => ActiveSequents seq
emptyActives = AS mempty

emptyInactives :: Ord seq => InactiveSequents seq
emptyInactives = IS mempty

emptyGlobalIndex :: Ord seq => GlobalIndex seq
emptyGlobalIndex = GI mempty

--------------------------------------------------------------------------------

{-| Type of elements that represent the result of applying an inference rule.

    Such application may either fail, succeed with a value (when the rule has
    been fully applied), or succeed with a function (when the rule is only
    partially applied and has still some premises to match). -}
type RuleRes seqty = Rel (ActiveSequent seqty) (ConclSequent seqty)

{-| Type of inference rules.
    Axioms are not considered rules in this case, so a rule takes at least one
    premise. Hence the corresponding type is a function from a premise sequent
    to a rule application result. -}
type Rule seqty = (ActiveSequent seqty) -> RuleRes seqty

--------------------------------------------------------------------------------
-- Operations

applyRule :: Rule seqty
          -> ActiveSequent seqty
          -> RuleRes seqty
applyRule rule s = rule s

foldActives
  :: (forall f. (Foldable f) => f (ActiveSequent seqty) -> b)
  -> ActiveSequents seqty
  -> b
foldActives folder (AS actives) = folder actives

isGoal
  :: ForwardSequent seqty
  => SearchSequent Goal seqty -> SearchSequent FSChecked seqty -> Maybe seqty
isGoal (GoalSS goal) (FSCheckedSS fss) =
  if fss `subsumes` goal
    then Just fss
    else Nothing

activate
  :: Ord seqty
  => ActiveSequents seqty
  -> InactiveSequent seqty
  -> (ActiveSequents seqty, ActiveSequent seqty)
activate (AS as) (InactiveSS s) = (AS (S.insert (ActiveSS s) as), ActiveSS s)

popInactiveOp
  :: Ord seqty
  => InactiveSequents seqty
  -> Maybe (InactiveSequents seqty, InactiveSequent seqty)
popInactiveOp (IS is) =
  case S.toList is of
    [] -> Nothing
    (x:xs) -> Just (IS . S.fromList $ xs, x)

addToIndex
  :: Ord seqty
  => GlobalIndex seqty -> SearchSequent BSChecked seqty -> GlobalIndex seqty
addToIndex (GI gi) (BSCheckedSS s) = GI (S.insert (GlIndexSS s) gi)

addToInactives
  :: Ord seqty
  => InactiveSequents seqty
  -> SearchSequent BSChecked seqty
  -> InactiveSequents seqty
addToInactives (IS ins) (BSCheckedSS s) = IS (S.insert (InactiveSS s) ins)

fwdSubsumes
  :: (ForwardSequent seqty, Show seqty)
  => GlobalIndex seqty
  -> SearchSequent Concl seqty
  -> Maybe (SearchSequent FSChecked seqty)
fwdSubsumes (GI globalIndex) (ConclSS s) =
  if or . S.map (\gi -> extractSequent gi `subsumes` s) $ globalIndex
    then Nothing
    else Just (FSCheckedSS s)

removeSubsumedByOp
  :: ForwardSequent seqty
  => SearchSequent FSChecked seqty
  -> InactiveSequents seqty
  -> (InactiveSequents seqty, SearchSequent BSChecked seqty)
removeSubsumedByOp (FSCheckedSS s) (IS is) =
  ( IS (S.filter (\iseq -> not (s `subsumes` (extractSequent iseq))) is)
  , BSCheckedSS s)

subsumesGoalOp
  :: (ForwardSequent goalty, MonadFail mf, Coercible seqty goalty)
  => SearchSequent FSChecked seqty -> SearchSequent Goal goalty -> mf seqty
subsumesGoalOp (FSCheckedSS s1) (GoalSS s2) =
  if (coerce s1) `subsumes` s2
    then return s1
    else Control.Monad.Fail.fail "sequent does not subsumes goal"

initialSequentsAndRules
  :: (Eq a, Eq l, Ord l, Ord a)
  => NeutralSequent l a
  -> (S.Set (SearchSequent Initial (DLSequent l a)), [Rule (DLSequent l a)])
initialSequentsAndRules =
  (S.map InitSS *** (map (dimap extractSequent (dimap extractSequent ConclSS)))) .
  Prover.Frontier.initialSequentsAndRules
