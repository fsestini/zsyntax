{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

module Prover where


import Control.Arrow
import Formula
import LabelledSequent
import Rule
import qualified Data.Set as S
import qualified Data.Map as M
import Filterable
import Relation
import Rel
import Prover.Class
import Prover.Transformer


processNewActive
  :: (Monad m, HasProverState l a m)
  => LabelledSequent l a -> m (RuleAppRes l a)
processNewActive sequent = do
  actives <- getActives
  rules <- getRules
  let r1 = applyAll rules sequent
      r2 = percolate actives . resRules $ r1
  return $ r1 `mappend` r2

type Derivation l a = LabelledSequent l a

filterUnsubsumed
  :: (HasProverState l a m, Monad m)
  => S.Set (LabelledSequent l a) -> m (S.Set (LabelledSequent l a))
filterUnsubsumed = undefined

otterLoop
  :: (Monad m, HasProverState l a m, HasProverEnvironment l a m)
  => m (Maybe (Derivation l a))
otterLoop = do
  -- TODO!!! check here if any inactive sequent subsumes the goal sequent
  inactive <- popInactive
  case inactive of
    Nothing -> return Nothing
    Just sequent -> do
      addActive sequent
      (seqs, rules) <- processNewActive sequent
      unsubSeqs <- filterUnsubsumed seqs
      addInactives unsubSeqs
      addRules rules
      return (Just sequent)
