{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Prover.Operations where
  -- ( RuleAppRes
  -- , resSequents
  -- , resRules
  -- , applyAll
  -- , applyToActives
  -- , percolate
  -- ) where

import LabelledSequent
import Rule
import qualified Data.Set as S

import Prover.Structures

applyAll :: (Ord l, Ord a) => [Rule l a] -> ActiveSequent l a -> RuleAppRes l a
applyAll rules as = partitionRuleRes . map ($ (extractSequent as)) $ rules

applyToActives
  :: (Ord l, Ord a)
  => ActiveSequents l a -> [Rule l a] -> RuleAppRes l a
applyToActives actives rules = partitionRuleRes $ concatMap mapper rules
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

haveGoal
  :: (Ord l, Ord a)
  => SearchSequent Goal l a
  -> [SearchSequent FSChecked l a]
  -> Maybe (LabelledSequent l a)
haveGoal _ [] = Nothing
haveGoal goal (s:ss) =
  if (extractSequent s) `subsumes` (extractSequent goal)
    then Just (extractSequent s)
    else haveGoal goal ss

activate
  :: (Ord l, Ord a)
  => ActiveSequents l a
  -> InactiveSequent l a
  -> (ActiveSequents l a, ActiveSequent l a)
activate as (InactiveSS s) = (S.insert (ActiveSS s) as, ActiveSS s)

addToIndex
  :: (Ord l, Ord a)
  => S.Set (SearchSequent GlIndex l a)
  -> SearchSequent BSChecked l a
  -> S.Set (SearchSequent GlIndex l a)
addToIndex gi (BSCheckedSS s) = S.insert (GlIndexSS s) gi

addToInactives
  :: (Ord l, Ord a)
  => InactiveSequents l a
  -> SearchSequent BSChecked l a
  -> InactiveSequents l a
addToInactives ins (BSCheckedSS s) = S.insert (InactiveSS s) ins

fwdSubsumes
  :: (Ord a, Ord l)
  => SearchSequent GlIndex l a
  -> SearchSequent Concl l a
  -> Maybe (SearchSequent FSChecked l a)
fwdSubsumes (GlIndexSS s1) (ConclSS s2) =
  if s1 `subsumes` s2
    then Nothing
    else Just (FSCheckedSS s2)

bwdSubsumes
  :: (Ord a, Ord l)
  => SearchSequent FSChecked l a -> InactiveSequent l a -> Bool
bwdSubsumes (FSCheckedSS s1) (InactiveSS s2) = s1 `subsumes` s2

subsumesGoal
  :: (Ord a, Ord l)
  => SearchSequent FSChecked l a -> SearchSequent Goal l a -> Bool
subsumesGoal (FSCheckedSS s1) (GoalSS s2) = s1 `subsumes` s2

-- filterUnsubsumed
--   :: (HasProverState l a m, Monad m)
--   => S.Set (LabelledSequent l a) -> m (S.Set (LabelledSequent l a))
-- filterUnsubsumed = undefined
