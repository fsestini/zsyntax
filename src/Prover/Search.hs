{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

module Prover.Search (doSearch, SearchConstraint, SearchMonad(..)) where

import Prelude hiding (fail, map)
import Data.Foldable
import Control.Monad
import Control.Arrow ((***))
import Rel (unRel)
import qualified Data.Set as S
import TypeClasses

import Prover.Class
import Prover.Structures
       (InactivesResult, NoInactivesReason(..), SearchSequent, Stage(..),
        Rule, ActiveSequent, ConclSequent, RuleRes, ActiveSequents,
        initialIsBSChecked, initialIsFSChecked, foldActives, applyRule)

import Debug.Trace

{-

  1. Compute frontier
  2. Compute initial set of rules ---> initial sequents
  3. Put initial sequents in inactive set
  4. Pop inactive sequent. If no more, exit with failure
  5. Put popped inactive in active set
  6. Apply all rules to sequent
  7. Percolate
  8. Add resulting sequents that are not subsumed by old inactive sequents
     (taken from the so-called global index) to inactive set (forward
     subsumption)
  9. Remove inactive sequents that are subsumed by the new sequents (backward
     subsumption)
  10. Add rules to rule set
  11. If any new sequent subsumes the goal, exit
  12. Add new sequents to inactive set
  13. Goto 4

-}

class MonadPlus m => SearchMonad m where
  failSaturated :: m a
  failThresholdBreak :: m a

type SearchConstraint m mf seqty =
  (Monad m, SearchMonad mf, HasProverState seqty m
   , HasProverEnvironment seqty m, Ord seqty, Eq seqty)

doSearch
  :: SearchConstraint m mf seqty
  => S.Set (SearchSequent 'Initial seqty) -> [Rule seqty] -> m (mf seqty)
doSearch initialSequents initialRules = do
  addInactives (fmap initialIsBSChecked initialList)
  addRules initialRules
  liftM2 mplus (haveGoal (fmap initialIsFSChecked initialList)) otterLoop
  where
    initialList = S.toList initialSequents

otterLoop :: SearchConstraint m mf seqty => m (mf seqty)
otterLoop = do
  inactive <- popInactive
  case inactive of
    Left Saturated -> return $ failSaturated
    Left ThresholdBreak -> return $ failThresholdBreak
    Right sequent ->
      do
        res <- processNewActive sequent
        subRes <- filterSubsequents (S.toList $ resSequents res)
        unsubSeqs <- filterUnsubsumed subRes
        unsubSeqs' <- removeSubsumedByAll unsubSeqs
        addInactives unsubSeqs'
        addRules (resRules res)
        liftM2 mplus (haveGoal unsubSeqs) otterLoop

processNewActive
  :: (Monad m, HasProverState seqty m, Ord seqty)
  => ActiveSequent seqty -> m (RuleAppRes seqty)
processNewActive sequent = do
  actives <- getActives
  rules <- getRules
  let r1 = applyAll rules sequent
      r2 = percolate actives . resRules $ r1
  return $ r1 `mappend` r2

--------------------------------------------------------------------------------

-- | Result type of matching a list of rules to an input sequent.
type RuleAppRes seqty = (S.Set (ConclSequent seqty), [Rule seqty])

resSequents :: RuleAppRes seqty -> S.Set (ConclSequent seqty)
resSequents r = fst r

resRules :: RuleAppRes seqty -> [Rule seqty]
resRules r = snd r

partitionRuleRes
  :: (Foldable f, Ord seqty)
  => f (RuleRes seqty) -> RuleAppRes seqty
partitionRuleRes =
  (S.fromList . toList *** toList) .
  partitionEithers . filterOut . fmap unRel . toList

applyAll
  :: (Ord seqty, Foldable f, CanPartitionEithers f)
  => f (Rule seqty) -> ActiveSequent seqty -> RuleAppRes seqty
applyAll rules as = partitionRuleRes . fmap ($ as) . toList $ rules

percolate
  :: Ord seqty
  => ActiveSequents seqty -> [Rule seqty] -> RuleAppRes seqty
percolate _ [] = mempty
percolate actives rules = r1 `mappend` r2
  where
    r1 = partitionRuleRes . concatMap mapper $ rules
    r2 = percolate actives . resRules $ r1
    mapper rule = foldActives (foldMap (pure . applyRule rule)) actives
