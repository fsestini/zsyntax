{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Prover where

import Formula
import Rule
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import qualified Data.Set as S
import qualified Data.Map as M
import Filterable
import Relation

newtype ActiveSequents l a = AS (S.Set (LabelledSequent l a))
newtype InactiveSequents l a = IS (S.Set (LabelledSequent l a))

newtype Formula a = F (forall p . LFormula p () a)

type ProverState l a = ([Rule l a], ActiveSequents l a, InactiveSequents l a)
type ProverEnvironment l a = (LabelledSequent l a, M.Map (Label l a) (Formula a))

type ProverT l a m b = ReaderT (ProverEnvironment l a) (StateT (ProverState l a) m) b

class HasProverState l a m where
  getRules :: m ([Rule l a])
  addRules :: [Rule l a] -> m ()
  --traverseActives :: (Traversable t) => (t (LabelledSequent l a) -> m b) -> m b
  popInactive :: m (Maybe (LabelledSequent l a))
  getActives :: m (ActiveSequents l a)
  addActive :: LabelledSequent l a -> m ()
  -- isSubsumed :: LabelledSequent l a -> m Bool
  -- removeSubsumed :: LabelledSequent l a -> m ()

applyAll :: [Rule l a]
         -> LabelledSequent l a
         -> ([LabelledSequent l a], [Rule l a])
applyAll rules sequent =
  fpartitionEithers . filterOut . fmap unRel $ map ($ sequent) rules

applyToActives :: ActiveSequents l a
               -> [Rule l a]
               -> (S.Set (LabelledSequent l a), [Rule l a])
applyToActives = undefined

percolate :: ActiveSequents l a -> [Rule l a] -> (S.Set (LabelledSequent l a), [Rule l a])
percolate actives [] = (S.empty, [])
percolate actives rules = let (resSeqs, resRules) = applyToActives actives rules
                              (recSeqs, recRules) = percolate actives resRules
                          in (resSeqs `S.union` recSeqs, resRules ++ recRules)

applySequentToAllRules
  :: (Filterable t, Traversable t, HasProverState l a m, Monad m)
  => LabelledSequent l a -> t (Rule l a) -> m ()
applySequentToAllRules sequent rules  = do
  results <- mapM (return . ($ sequent)) rules
  let (x, y) = filterPartitionRel results
  undefined

class HasProverEnvironment l a m where
  subsumesGoal :: LabelledSequent l a -> m Bool

type Derivation l a = LabelledSequent l a

otterLoop
  :: (Monad m, HasProverState l a m, HasProverEnvironment l a m)
  => m (Maybe (Derivation l a))
otterLoop = do
  -- check here if any inactive sequent subsumes the goal sequent
  inactive <- popInactive
  case inactive of
    Nothing -> return Nothing
    Just sequent -> return (Just sequent)
