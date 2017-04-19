{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Prover.Class where

import Data.Foldable
import Formula
import LabelledSequent
import Rule
import TypeClasses
import Control.Applicative
import Control.Monad

import Prover.Structures

-- The prover state must include a global index of all sequents that have been
-- added to the inactive set.
class HasProverState l a m where
  getRules :: m ([Rule l a])
  addRule :: Rule l a -> m ()
  addInactive :: SearchSequent BSChecked l a -> m ()
  popInactive :: m (Maybe (ActiveSequent l a))
  getActives :: m (ActiveSequents l a)
  isNotFwdSubsumed :: ConclSequent l a
                   -> m (Maybe (SearchSequent FSChecked l a))
  removeSubsumedBy :: SearchSequent FSChecked l a
                   -> m (SearchSequent BSChecked l a)

class HasProverEnvironment l a m where
  getGoal :: m (Sequent l a)
  subsumesGoal :: SearchSequent FSChecked l a -> m (Maybe (LabelledSequent l a))

haveGoal
  :: (Monad m, HasProverEnvironment l a m, Foldable f)
  => f (SearchSequent FSChecked l a) -> m (Maybe (LabelledSequent l a))
haveGoal = foldrM folder Nothing
  where
    folder ss rest = liftM2 (<|>) (subsumesGoal ss) (return rest)

addInactives
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (SearchSequent BSChecked l a) -> m ()
addInactives = mapM_ addInactive

addRules
  :: (Traversable t, Monad m, HasProverState l a m)
  => t (Rule l a) -> m ()
addRules = mapM_ addRule

removeSubsumedByAll
  :: (Monad m, Traversable t, HasProverState l a m)
  => t (SearchSequent FSChecked l a) -> m (t (SearchSequent BSChecked l a))
removeSubsumedByAll = mapM removeSubsumedBy

filterUnsubsumed
  :: (HasProverState l a m, Monad m)
  => [ConclSequent l a] -> m [SearchSequent FSChecked l a]
filterUnsubsumed = fmap filterOut . mapM isNotFwdSubsumed
