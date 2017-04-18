{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

module Prover.Operations
  ( RuleAppRes
  , resSequents
  , resRules
  , applyAll
  , applyToActives
  , percolate
  ) where

import Control.Arrow
import LabelledSequent
import Rule
import qualified Data.Set as S
import Filterable
import Rel
import Prover.Class

--------------------------------------------------------------------------------

-- | Result type of matching a list of rules to an input sequent.
newtype RuleAppRes l a =
  RAR (S.Set (LabelledSequent l a), [Rule l a])
  deriving (Monoid)

-- instance Monoid (RuleAppRes l a) where
--   mempty = (S.empty, [])
--   mappend (s1, l1) (s2, l2) = (s1 `S.union` s2, l1 ++ )

resSequents :: RuleAppRes l a -> S.Set (LabelledSequent l a)
resSequents (RAR r) = fst r

resRules :: RuleAppRes l a -> [Rule l a]
resRules (RAR r) = snd r

--------------------------------------------------------------------------------

partitionRuleRes :: (Ord l, Ord a) => [RuleRes l a] -> RuleAppRes l a
partitionRuleRes =
  RAR . (S.fromList *** id) . fpartitionEithers . filterOut . fmap unRel

--------------------------------------------------------------------------------

applyAll :: (Ord l, Ord a) => [Rule l a] -> LabelledSequent l a -> RuleAppRes l a
applyAll rules sequent = partitionRuleRes . map ($ sequent) $ rules

applyToActives
  :: (Ord l, Ord a)
  => ActiveSequents l a -> [Rule l a] -> RuleAppRes l a
applyToActives actives rules = partitionRuleRes $ concatMap mapper rules
  where
    mapper rule = fmap (rule . activeIsLabelled) . S.toList $ actives

percolate
  :: (Ord l, Ord a)
  => ActiveSequents l a -> [Rule l a] -> RuleAppRes l a
percolate _ [] = RAR (S.empty, [])
percolate actives rules = r1 `mappend` r2
  where
    r1 = applyToActives actives rules
    r2 = percolate actives . resRules $ r1

filterUnsubsumed
  :: (HasProverState l a m, Monad m)
  => S.Set (LabelledSequent l a) -> m (S.Set (LabelledSequent l a))
filterUnsubsumed = undefined
