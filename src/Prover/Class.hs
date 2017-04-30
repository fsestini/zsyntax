{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Prover.Class where

import Data.Foldable
-- import Formula
-- import Relation
-- import Rule
import TypeClasses
import Control.Applicative
import Control.Monad

import Prover.Structures

-- The prover state must include a global index of all sequents that have been
-- added to the inactive set.
class HasProverState seqty m where
  getRules :: m ([Rule seqty])
  addRule :: Rule seqty -> m ()
  addInactive :: SearchSequent BSChecked seqty -> m ()
  popInactive :: m (Maybe (ActiveSequent seqty))
  getActives :: m (ActiveSequents seqty)
  isNotFwdSubsumed :: ConclSequent seqty
                   -> m (Maybe (SearchSequent FSChecked seqty))
  removeSubsumedBy :: SearchSequent FSChecked seqty
                   -> m (SearchSequent BSChecked seqty)

class HasProverEnvironment seqty m where
  -- getGoal :: m (NeutralSequent l a)
  subsumesGoal :: SearchSequent FSChecked seqty -> m (Maybe seqty)

haveGoal
  :: (Monad m, HasProverEnvironment seqty m, Foldable f)
  => f (SearchSequent FSChecked seqty) -> m (Maybe seqty)
haveGoal = foldrM folder Nothing
  where
    folder ss rest = liftM2 (<|>) (subsumesGoal ss) (return rest)

addInactives
  :: (Traversable t, Monad m, HasProverState seqty m)
  => t (SearchSequent BSChecked seqty) -> m ()
addInactives = mapM_ addInactive

addRules
  :: (Traversable t, Monad m, HasProverState seqty m)
  => t (Rule seqty) -> m ()
addRules = mapM_ addRule

removeSubsumedByAll
  :: (Monad m, Traversable t, HasProverState seqty m)
  => t (SearchSequent FSChecked seqty) -> m (t (SearchSequent BSChecked seqty))
removeSubsumedByAll = mapM removeSubsumedBy

filterUnsubsumed
  :: (HasProverState seqty m, Monad m, Traversable t, CanPartitionEithers t)
  => t (ConclSequent seqty) -> m (t (SearchSequent FSChecked seqty))
filterUnsubsumed = fmap filterOut . mapM isNotFwdSubsumed
