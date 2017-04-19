{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Prover.Structures
  ( Stage(..)
  , SearchSequent
  , ActiveSequent
  , InactiveSequent
  , ActiveSequents
  , InactiveSequents
  , ConclSequent
  , GlobalIndex
  , RuleAppRes
  , resRules
  , resSequents
  , applyAll
  , percolate
  , Rule
  , RuleRes
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
  ) where

import Control.Arrow
import LabelledSequent
import qualified Data.Set as S
import Rel
import Prover.Frontier (initialSequentsAndRules)
import Formula

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

data SearchSequent :: Stage -> * -> * -> * where
  InitSS :: LabelledSequent l a -> SearchSequent Initial l a
  ActiveSS :: LabelledSequent l a -> SearchSequent Active l a
  InactiveSS :: LabelledSequent l a -> SearchSequent Inactive l a
  ConclSS :: LabelledSequent l a -> SearchSequent Concl l a
  FSCheckedSS :: LabelledSequent l a -> SearchSequent FSChecked l a
  BSCheckedSS :: LabelledSequent l a -> SearchSequent BSChecked l a
  GlIndexSS :: LabelledSequent l a -> SearchSequent GlIndex l a
  GoalSS :: LabelledSequent l a -> SearchSequent Goal l a

extractSequent :: SearchSequent s l a -> LabelledSequent l a
extractSequent (InitSS s) = s
extractSequent (ActiveSS s) = s
extractSequent (InactiveSS s) = s
extractSequent (ConclSS s) = s
extractSequent (BSCheckedSS s) = s
extractSequent (FSCheckedSS s) = s

instance (Eq a, Eq l) => Eq (SearchSequent s l a) where
  s1 == s2 = (extractSequent s1) == (extractSequent s2)

instance (Ord a, Ord l) => Ord (SearchSequent s l a) where
  compare s1 s2 = compare (extractSequent s1) (extractSequent s2)

type ActiveSequent l a = SearchSequent Active l a
newtype ActiveSequents l a = AS (S.Set (SearchSequent Active l a))
type InactiveSequent l a = SearchSequent Inactive l a
newtype InactiveSequents l a = IS (S.Set (InactiveSequent l a))
type ConclSequent l a = SearchSequent Concl l a
newtype GlobalIndex l a = GI (S.Set (SearchSequent GlIndex l a))

--------------------------------------------------------------------------------

initialize :: LabelledSequent l a -> SearchSequent Initial l a
initialize = InitSS

initialIsFSChecked :: SearchSequent Initial l a -> SearchSequent FSChecked l a
initialIsFSChecked (InitSS s) = FSCheckedSS s

initialIsBSChecked :: SearchSequent Initial l a -> SearchSequent BSChecked l a
initialIsBSChecked (InitSS s) = BSCheckedSS s

--------------------------------------------------------------------------------

-- | Result type of matching a list of rules to an input sequent.
newtype RuleAppRes l a =
  RAR (S.Set (SearchSequent Concl l a), [Rule l a])
  deriving (Monoid)
{-| Type of elements that represent the result of applying an inference rule.

resSequents :: RuleAppRes l a -> S.Set (SearchSequent Concl l a)
resSequents (RAR r) = fst r
    Such application may either fail, succeed with a value (when the rule has
    been fully applied), or succeed with a function (when the rule is only
    partially applied and has still some premises to match). -}
type RuleRes l a = Rel (LabelledSequent l a) (ConclSequent l a)

resRules :: RuleAppRes l a -> [Rule l a]
resRules (RAR r) = snd r

partitionRuleRes
  :: (Ord l, Ord a)
  => [RuleRes l a] -> RuleAppRes l a
partitionRuleRes =
  RAR .
  (S.fromList . map ConclSS *** id) . fpartitionEithers . filterOut . fmap unRel
{-| Type of inference rules.
    Axioms are not considered rules in this case, so a rule takes at least one
    premise. Hence the corresponding type is a function from a premise sequent
    to a rule application result. -}
type Rule l a = (LabelledSequent l a) -> RuleRes l a

--------------------------------------------------------------------------------
-- Operations

applyAll :: (Ord l, Ord a) => [Rule l a] -> ActiveSequent l a -> RuleAppRes l a
applyAll rules as = partitionRuleRes . map ($ (extractSequent as)) $ rules

applyToActives
  :: (Ord l, Ord a)
  => ActiveSequents l a -> [Rule l a] -> RuleAppRes l a
applyToActives (AS actives) rules = partitionRuleRes $ concatMap mapper rules
  where
    mapper rule = fmap (rule . extractSequent) . S.toList $ actives

percolate
  :: (Ord l, Ord a)
  => ActiveSequents l a -> [Rule l a] -> RuleAppRes l a
percolate _ [] = RAR (S.empty, [])
percolate actives rules = r1 `mappend` r2
  where
    r1 = applyToActives actives rules
    r2 = percolate actives . resRules $ r1

haveGoalOp
  :: (Ord l, Ord a)
  => SearchSequent Goal l a
  -> [SearchSequent FSChecked l a]
  -> Maybe (LabelledSequent l a)
haveGoalOp _ [] = Nothing
haveGoalOp goal (s:ss) =
  if (extractSequent s) `subsumes` (extractSequent goal)
    then Just (extractSequent s)
    else haveGoalOp goal ss

activate
  :: (Ord l, Ord a)
  => ActiveSequents l a
  -> InactiveSequent l a
  -> (ActiveSequents l a, ActiveSequent l a)
activate (AS as) (InactiveSS s) = (AS (S.insert (ActiveSS s) as), ActiveSS s)

popInactiveOp :: (Ord a, Ord l) => InactiveSequents l a
              -> Maybe (InactiveSequents l a, InactiveSequent l a)
popInactiveOp (IS is) =
  case S.toList is of
    [] -> Nothing
    (x:xs) -> Just (IS . S.fromList $ xs, x)

addToIndex
  :: (Ord l, Ord a)
  => GlobalIndex l a
  -> SearchSequent BSChecked l a
  -> GlobalIndex l a
addToIndex (GI gi) (BSCheckedSS s) = GI (S.insert (GlIndexSS s) gi)

addToInactives
  :: (Ord l, Ord a)
  => InactiveSequents l a
  -> SearchSequent BSChecked l a
  -> InactiveSequents l a
addToInactives (IS ins) (BSCheckedSS s) = IS (S.insert (InactiveSS s) ins)

fwdSubsumes
  :: (Ord a, Ord l)
  => GlobalIndex l a
  -> SearchSequent Concl l a
  -> Maybe (SearchSequent FSChecked l a)
fwdSubsumes (GI globalIndex) (ConclSS s) =
  if or . S.map (\gi -> (extractSequent gi) `subsumes` s) $ globalIndex
    then Nothing
    else Just (FSCheckedSS s)

removeSubsumedByOp
  :: (Ord a, Ord l)
  => SearchSequent FSChecked l a
  -> InactiveSequents l a
  -> (InactiveSequents l a, SearchSequent BSChecked l a)
removeSubsumedByOp (FSCheckedSS s) (IS is) =
  ( IS (S.filter (\iseq -> not (s `subsumes` (extractSequent iseq))) is)
  , BSCheckedSS s)

subsumesGoalOp
  :: (Ord a, Ord l)
  => SearchSequent FSChecked l a
  -> SearchSequent Goal l a
  -> Maybe (LabelledSequent l a)
subsumesGoalOp (FSCheckedSS s1) (GoalSS s2) =
  if s1 `subsumes` s2
    then Just s1
    else Nothing

initialSequentsAndRules
  :: (Eq a, Eq l, Ord l, Ord a)
  => Sequent l a
  -> (S.Set (SearchSequent Initial l a), [Rule l a])
initialSequentsAndRules =
  (S.map InitSS *** fmap (fmap (fmap ConclSS))) .
  Prover.Frontier.initialSequentsAndRules
