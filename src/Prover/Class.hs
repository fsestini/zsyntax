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
  isNotFwdSubsumed :: ConclSequent seqty
                   -> m (Maybe (SearchSequent FSChecked seqty))
  removeSubsumedBy :: SearchSequent FSChecked seqty
                   -> m (SearchSequent BSChecked seqty)

class HasProverEnvironment seqty proof m where
  subsumesGoal
    :: (MonadPlus mf, LogMonad m)
    => SearchSequent FSChecked seqty -> m (mf proof)

haveGoal
  :: ( MonadPlus mf
     , LogMonad m
     , HasProverEnvironment seqty proof m
     , Foldable f
     -- , SearchTriple seqty goalty proof
     )
  => f (SearchSequent FSChecked seqty) -> m (mf proof)
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
  => t (ConclSequent seqty) -> m [SearchSequent FSChecked seqty]
filterUnsubsumed = fmap filterOut . mapM isNotFwdSubsumed . toList

-- filterSubsequents
--   :: ( HasProverEnvironment seqty goalty m
--      , Monad m
--      , Traversable t
--      , Foldable t
--      , CanPartitionEithers t
--      )
--   => t (ConclSequent seqty) -> m [SearchSequent SSChecked seqty]
-- filterSubsequents = fmap filterOut . mapM isSubsequent
