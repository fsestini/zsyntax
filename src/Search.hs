{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

module Search where

import Data.Foldable
import Prelude hiding (map)
import Control.Applicative
import Control.Arrow
import qualified Data.Set as S
import Prover.Frontier
import LabelledSequent
import TypeClasses
import Rel
import Prover

-- TODO: use the real thing
type DerivationTerm l a = LabelledSequent l a

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
  11. Is any new sequent subsumed the goal, exit
  12. Add new sequents to inactive set
  13. Goto 4

-}

doSearch
  :: forall m a l.
     ( Monad m
     , HasProverState l a m
     , HasProverEnvironment l a m
     , Ord l
     , Ord a
     , Eq a
     , Eq l
     )
  => m (Maybe (DerivationTerm l a))
doSearch = do
  goal <- getGoal @l @a
  let (initialSequents, initialRules) =
        (S.toList *** id) . initialSequentsAndRules $ goal
  addInactives (map initialIsBSChecked initialSequents)
  addRules initialRules
  (<|>) <$> (haveGoal (map initialIsFSChecked initialSequents)) <*> otterLoop

otterLoop
  :: forall m l a.
     ( Monad m
     , HasProverState l a m
     , HasProverEnvironment l a m
     , Ord a
     , Ord l
     , Eq a
     , Eq l
     )
  => m (Maybe (DerivationTerm l a))
otterLoop = do
  inactive <- popInactive
  case inactive of
    Nothing -> return Nothing
    Just sequent -> do
      res <- processNewActive @m @l @a sequent
      unsubSeqs <- filterUnsubsumed (S.toList . resSequents $ res)
      unsubSeqs' <- removeSubsumedByAll unsubSeqs
      addInactives unsubSeqs'
      addRules (resRules res)
      (<|>) <$> (haveGoal unsubSeqs) <*> otterLoop

processNewActive
  :: (Monad m, HasProverState l a m, Ord l, Ord a)
  => ActiveSequent l a -> m (RuleAppRes l a)
processNewActive sequent = do
  actives <- getActives
  rules <- getRules
  let r1 = applyAll rules sequent
      r2 = percolate actives . resRules $ r1
  return $ r1 `mappend` r2

--------------------------------------------------------------------------------

-- | Result type of matching a list of rules to an input sequent.
type RuleAppRes l a = (S.Set (ConclSequent l a), [Rule l a])

resSequents :: RuleAppRes l a -> S.Set (ConclSequent l a)
resSequents r = fst r

resRules :: RuleAppRes l a -> [Rule l a]
resRules r = snd r

partitionRuleRes
  :: (CanMap f, CanPartitionEithers f, Foldable f, Ord l, Ord a)
  => f (RuleRes l a) -> RuleAppRes l a
partitionRuleRes =
  (S.fromList . toList *** toList) . partitionEithers . filterOut . map unRel

applyAll
  :: (Ord a, Ord l, Foldable f, CanPartitionEithers f, CanMap f)
  => f (Rule l a) -> ActiveSequent l a -> RuleAppRes l a
applyAll rules as = partitionRuleRes . map ($ (extractSequent as)) $ rules

applyToActives
  :: (Ord l, Ord a, Foldable f)
  => ActiveSequents l a -> f (Rule l a) -> RuleAppRes l a
applyToActives actives rules = partitionRuleRes $ concatMap mapper rules
  where
    mapper rule = foldActives (foldMap (pure . applyRule rule)) actives

percolate
  :: (Ord l, Ord a, Foldable f)
  => ActiveSequents l a -> f (Rule l a) -> RuleAppRes l a
percolate actives rules = r1 `mappend` r2
  where
    r1 = applyToActives actives rules
    r2 = percolate actives . resRules $ r1
