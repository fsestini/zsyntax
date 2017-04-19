{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Prover.Structures where

import Filterable
import Control.Arrow
import LabelledSequent
import qualified Data.Set as S
import Rule
import Rel

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
type ActiveSequents l a = S.Set (SearchSequent Active l a)
type InactiveSequent l a = SearchSequent Inactive l a
type InactiveSequents l a = S.Set (InactiveSequent l a)
type ConclSequent l a = SearchSequent Concl l a

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

resSequents :: RuleAppRes l a -> S.Set (SearchSequent Concl l a)
resSequents (RAR r) = fst r

resRules :: RuleAppRes l a -> [Rule l a]
resRules (RAR r) = snd r

partitionRuleRes :: (Ord l, Ord a) => [RuleRes l a] -> RuleAppRes l a
partitionRuleRes =
  RAR . (S.fromList . map ConclSS *** id) . fpartitionEithers . filterOut . fmap unRel
