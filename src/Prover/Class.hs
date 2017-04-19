{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Prover.Class where

import Formula
import LabelledSequent
import Rule
import Filterable

import Prover.Structures

-- The prover state must include a global index of all sequents that have been
-- added to the inactive set.
class HasProverState l a m where
  getRules :: m ([Rule l a])
  addRule :: Rule l a -> m ()
  addInactive :: SearchSequent BSChecked l a -> m ()
  popInactive :: m (Maybe (ActiveSequent l a))
  getActives :: m (ActiveSequents l a)
  removeSubsumedBy :: SearchSequent FSChecked l a -> m ()
  isNotFwdSubsumed :: ConclSequent l a
                   -> m (Maybe (SearchSequent FSChecked l a))

class HasProverEnvironment l a m where
  getGoal :: m (Sequent l a)
  subsumesGoal :: SearchSequent FSChecked l a -> m Bool

haveGoal
  :: (Monad m, HasProverEnvironment l a m)
  => [LabelledSequent l a] -> m (Maybe (LabelledSequent l a))
haveGoal [] = return Nothing
haveGoal (sequent:rest) = do
  res <- subsumesGoal sequent
  case res of
    True -> return . Just $ sequent
    False -> haveGoal rest

addActives
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (ActiveSequent l a) -> m ()
addActives = mapM_ addActive

addInactives
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (SearchSequent BSChecked l a) -> m ()
addInactives = mapM_ addInactive

addRules
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (Rule l a) -> m ()
addRules = mapM_ addRule

removeSubsumedByAll
  :: (Monad m, Traversable f, HasProverState l a m)
  => f (SearchSequent FSChecked l a) -> m ()
removeSubsumedByAll = mapM_ removeSubsumedBy

filterUnsubsumed
  :: (HasProverState l a m, Monad m)
  => [ConclSequent l a] -> m [SearchSequent FSChecked l a]
filterUnsubsumed = fmap filterOut . mapM isNotFwdSubsumed
