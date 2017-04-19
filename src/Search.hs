{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

module Search where

import Control.Applicative
import Control.Arrow
import qualified Data.Set as S
import Prover.Frontier
import LabelledSequent

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
      addActive sequent
      res <- processNewActive @m @l @a sequent
      unsubSeqs <- filterUnsubsumed (S.toList . resSequents $ res)
      removeSubsumedByAll unsubSeqs
      addInactives unsubSeqs
      addRules (resRules res)
      (<|>) <$> (haveGoal unsubSeqs) <*> otterLoop

processNewActive
  :: (Monad m, HasProverState l a m, Ord l, Ord a)
  => ActiveSequent l a -> m (RuleAppRes l a)
processNewActive sequent = do
  actives <- getActives
  rules <- getRules
  let r1 = applyAll rules (activeIsLabelled sequent)
      r2 = percolate actives . resRules $ r1
  return $ r1 `mappend` r2
