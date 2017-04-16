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

applyAll :: [Rule l a]
         -> LabelledSequent l a
         -> (S.Set (LabelledSequent l a), [Rule l a])
applyAll rules sequent = partitionRuleRes . map ($ sequent) $ rules

partitionRuleRes :: [RuleRes l a] -> (S.Set (LabelledSequent l a), [Rule l a])
partitionRuleRes =
  (S.fromList *** id) . fpartitionEithers . filterOut . fmap unRel

applyToActives :: ActiveSequents l a
               -> [Rule l a]
               -> (S.Set (LabelledSequent l a), [Rule l a])
applyToActives (AS actives) rules =
  partitionRuleRes $ concatMap (mapper actives) rules
  where
    mapper actives rule = fmap rule . S.toList $ actives

percolate :: ActiveSequents l a
          -> [Rule l a]
          -> (S.Set (LabelledSequent l a), [Rule l a])
percolate actives [] = (S.empty, [])
percolate actives rules = (resSeqs `S.union` recSeqs, resRules ++ recRules)
  where
    (resSeqs, resRules) = applyToActives actives rules
    (recSeqs, recRules) = percolate actives resRules

processNewActive
  :: (Monad m, HasProverState l a m)
  => LabelledSequent l a -> m (S.Set (LabelledSequent l a), [Rule l a])
processNewActive sequent = do
  actives <- getActives
  rules <- getRules
  let (seqs, newRules) = applyAll rules sequent
      (moarSeqs, moarRules) = percolate actives newRules
  return (seqs `S.union` moarSeqs, newRules ++ moarRules)

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
