{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Prover.Class where

import Data.Foldable
import TypeClasses
import Control.Monad hiding (fail)
import Prelude hiding (fail)
import Control.Applicative

import Prover.Structures
       (SearchSequent, Stage(..), ActiveSequent, ActiveSequents,
        ConclSequent, Rule, InactivesResult)

-- The prover state must include a global index of all sequents that have been
-- added to the inactive set.
class HasProverState seqty m where
  getRules :: m ([Rule seqty])
  addRule :: Rule seqty -> m ()
  addInactive :: SearchSequent BSChecked seqty -> m ()
  popInactive :: m (InactivesResult (ActiveSequent seqty))
  getActives :: m (ActiveSequents seqty)
  isNotFwdSubsumed :: SearchSequent SSChecked seqty
                   -> m (Maybe (SearchSequent FSChecked seqty))
  removeSubsumedBy :: SearchSequent FSChecked seqty
                   -> m (SearchSequent BSChecked seqty)

class HasProverEnvironment seqty m where
  isSubsequent
    :: MonadPlus mf
    => ConclSequent seqty -> m (mf (SearchSequent SSChecked seqty))
  subsumesGoal
    :: MonadPlus mf
    => SearchSequent FSChecked seqty -> m (mf seqty)

haveGoal
  :: ( Monad m
     , MonadPlus mf
     , HasProverEnvironment seqty m
     , Foldable f
     )
  => f (SearchSequent FSChecked seqty) -> m (mf seqty)
haveGoal = fmap (foldr (<|>) mzero) . mapM subsumesGoal . toList

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
  :: (HasProverState seqty m, Monad m, Foldable t)
  => t (SearchSequent SSChecked seqty) -> m [SearchSequent FSChecked seqty]
filterUnsubsumed = fmap filterOut . mapM isNotFwdSubsumed . toList

filterSubsequents
  :: ( HasProverEnvironment seqty m
     , Monad m
     , Traversable t
     , Foldable t
     , CanPartitionEithers t
     )
  => t (ConclSequent seqty) -> m [SearchSequent SSChecked seqty]
filterSubsequents = fmap filterOut . mapM isSubsequent
