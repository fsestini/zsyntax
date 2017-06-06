{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Prover.Structures
  ( Stage(..)
  , SearchSequent
  , ActiveSequent
  , InactiveSequent
  , ActiveSequents
  , InactiveSequents
  , ConclSequent
  , GlobalIndex
  , Rule
  , RuleRes
  , SearchTriple(..)
  , applyRule
  , initialIsFSChecked
  , initialIsBSChecked
  , initialize
  , subsumesGoalOp
  , removeSubsumedByOp
  , fwdSubsumes
  , activate
  , popInactiveOp
  , addToInactives
  -- , addToIndex
  , foldActives
  --, isGoal
  , makeGoal
  , emptyActives
  , emptyInactives
  , emptyGlobalIndex
  , toProverRules
  , InactivesResult
  , NoInactivesReason(..)
  ) where

import Data.Profunctor
import Prelude hiding (fail)
import Rel
import ForwardSequent
import Control.Monad (MonadPlus(..))
import qualified Data.Dequeue as D
import Data.Foldable
import TypeClasses (LogMonad)

--------------------------------------------------------------------------------

class ForwardSequent seqty =>
      SearchTriple seqty goalty proof | seqty -> proof where
  subsumesGoal
    :: (LogMonad ml, MonadPlus mp)
    => seqty -> goalty -> ml (mp proof)

--------------------------------------------------------------------------------
-- Types.

data Stage
  = Initial    -- | Initial sequent
  | Active     -- | Active sequent
  | Inactive   -- | Inactive sequent
  | Concl      -- | Conclusion sequent
  | FSChecked  -- | Forward subsumption-checked
  | BSChecked  -- | Backward subsumption-checked
  | GlIndex    -- | Global index sequent
  | Goal       -- | Goal sequent

data SearchSequent :: Stage -> * -> * where
  InitSS :: seq -> SearchSequent Initial seq
  ActiveSS :: seq -> SearchSequent Active seq
  InactiveSS :: seq -> SearchSequent Inactive seq
  ConclSS :: seq -> SearchSequent Concl seq
  FSCheckedSS :: seq -> SearchSequent FSChecked seq
  BSCheckedSS :: seq -> SearchSequent BSChecked seq
  GoalSS :: seq -> SearchSequent Goal seq

instance Show b => Show (SearchSequent a b) where
  show (InitSS s) = show s
  show (ActiveSS s) = show s
  show (InactiveSS s) = show s
  show (ConclSS s) = show s
  show (BSCheckedSS s) = show s
  show (FSCheckedSS s) = show s
  show (GoalSS s) = show s

extractSequent :: SearchSequent s seq -> seq
extractSequent (InitSS s) = s
extractSequent (ActiveSS s) = s
extractSequent (InactiveSS s) = s
extractSequent (ConclSS s) = s
extractSequent (BSCheckedSS s) = s
extractSequent (FSCheckedSS s) = s
extractSequent (GoalSS s) = s

instance Eq seq => Eq (SearchSequent s seq) where
  s1 == s2 = (extractSequent s1) == (extractSequent s2)

instance Ord seq => Ord (SearchSequent s seq) where
  compare s1 s2 = compare (extractSequent s1) (extractSequent s2)

instance ForwardSequent seq => ForwardSequent (SearchSequent s seq) where
  subsumes s1 s2 = subsumes (extractSequent s1) (extractSequent s2)

data NoInactivesReason = Saturated | ThresholdBreak

type ActiveSequent seq = SearchSequent Active seq
newtype ActiveSequents seq = AS [SearchSequent Active seq]
type InactiveSequent seq = SearchSequent Inactive seq
data InactiveSequents seq =
  IS NoInactivesReason
     (D.BankersDequeue (InactiveSequent seq))
type ConclSequent seq = SearchSequent Concl seq
data GlobalIndex seq = GI Int [seq]

instance Foldable GlobalIndex where
  foldr f z (GI _ l) = foldr f z l

--------------------------------------------------------------------------------

initialize :: seqty -> SearchSequent Initial seqty
initialize = InitSS

initialIsFSChecked :: SearchSequent Initial seqty
                   -> SearchSequent FSChecked seqty
initialIsFSChecked (InitSS s) = FSCheckedSS s

initialIsBSChecked :: SearchSequent Initial seqty
                   -> SearchSequent BSChecked seqty
initialIsBSChecked (InitSS s) = BSCheckedSS s

makeGoal :: seqty -> SearchSequent Goal seqty
makeGoal = GoalSS

emptyActives :: Ord seq => ActiveSequents seq
emptyActives = AS mempty

emptyInactives :: Ord seq => InactiveSequents seq
emptyInactives = IS Saturated D.empty

emptyGlobalIndex :: Ord seq => GlobalIndex seq
emptyGlobalIndex = GI 0 mempty

--------------------------------------------------------------------------------

{-| Type of elements that represent the result of applying an inference rule.

    Such application may either fail, succeed with a value (when the rule has
    been fully applied), or succeed with a function (when the rule is only
    partially applied and has still some premises to match). -}
type RuleRes seqty = Rel (ActiveSequent seqty) (ConclSequent seqty)

{-| Type of inference rules.
    Axioms are not considered rules in this case, so a rule takes at least one
    premise. Hence the corresponding type is a function from a premise sequent
    to a rule application result. -}
type Rule seqty = (ActiveSequent seqty) -> RuleRes seqty

type InactivesResult a = Either NoInactivesReason a

--------------------------------------------------------------------------------
-- Operations

applyRule :: Rule seqty
          -> ActiveSequent seqty
          -> RuleRes seqty
applyRule rule s = rule s

foldActives
  :: (forall f. (Foldable f) => f (ActiveSequent seqty) -> b)
  -> ActiveSequents seqty
  -> b
foldActives folder (AS actives) = folder actives

activate
  :: Ord seqty
  => ActiveSequents seqty
  -> InactiveSequent seqty
  -> (ActiveSequents seqty, ActiveSequent seqty)
activate (AS as) (InactiveSS s) = (AS (ActiveSS s : as), ActiveSS s)

popInactiveOp
  :: Ord seqty
  => InactiveSequents seqty
  -> InactivesResult (InactiveSequents seqty, InactiveSequent seqty)
popInactiveOp (IS r is) =
  case D.popFront is of
    Just (x, xs) -> Right (IS r xs, x)
    Nothing -> Left r

-- addToIndex
--   :: (Ord seqty)
--   => GlobalIndex seqty
--   -> SearchSequent BSChecked seqty
--   -> SearchResult (GlobalIndex seqty)
-- addToIndex (GI n gi) (BSCheckedSS s) =
--   if n + 1 <= 2000
--     then Ok (GI (n + 1) (S.insert s gi))
--     else OutOfSequents

addToInactives
  :: Ord seqty
  => InactiveSequents seqty
  -> GlobalIndex seqty
  -> SearchSequent BSChecked seqty
  -> (InactiveSequents seqty, GlobalIndex seqty)
addToInactives (IS r ins) (GI n gi) (BSCheckedSS s) =
  if n + 1 <= 2000
     then (IS r (D.pushBack ins (InactiveSS s)), (GI (n + 1) (s : gi)))
     else (IS ThresholdBreak ins, GI n gi)

fwdSubsumes
  :: (ForwardSequent seqty, Ord seqty)
  => GlobalIndex seqty
  -> SearchSequent Concl seqty
  -> Maybe (SearchSequent FSChecked seqty)
fwdSubsumes (GI _ globalIndex) (ConclSS s) =
  if or . map (\gi -> gi `subsumes` s) $ globalIndex
    then Nothing
    else Just (FSCheckedSS s)

removeSubsumedByOp
  :: ForwardSequent seqty
  => SearchSequent FSChecked seqty
  -> InactiveSequents seqty
  -> (InactiveSequents seqty, SearchSequent BSChecked seqty)
removeSubsumedByOp (FSCheckedSS s) (IS r is) =
  ( IS r (D.fromList . filter filterer . toList $ is), BSCheckedSS s)
  where
    filterer = \iseq -> not (s `subsumes` (extractSequent iseq))

subsumesGoalOp
  :: (MonadPlus mf, SearchTriple seqty goalty proof)
  => SearchSequent FSChecked seqty -> SearchSequent Goal goalty -> mf proof
subsumesGoalOp (FSCheckedSS s1) (GoalSS s2) =
  maybe mzero return (s1 `subsumesGoal` s2)

toProverRules :: (seqty -> Rel seqty seqty) -> Rule seqty
toProverRules = dimap extractSequent (dimap extractSequent ConclSS)
