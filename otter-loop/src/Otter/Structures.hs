{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC
  -Wall -Wno-unticked-promoted-constructors -Wno-redundant-constraints
  -Wno-unused-matches -Wno-unused-imports #-}

module Otter.Structures
  ( Stage(..)
  , SearchNode
  , ActiveNode
  , FSCheckedNode
  , BSCheckedNode
  , InactiveNode
  , ActiveNodes
  , InactiveNodes
  , ConclNode
  , GlobalIndex
  , Rule
  , RuleRes
  , Subsumable(..)
  -- , OrdSearchGoal(..)
  , applyRule
  , initIsFSCheckd
  , initIsBSCheckd
  , initialize
  -- , subsumesGoalOp
  , removeSubsumedByOp
  , fwdSubsumes
  , activate
  , popInactiveOp
  , addToInactives
  , foldActives
  , mkGoal
  , emptyActives
  , emptyInactives
  , emptyGI
  , toProverRules
  , extractNode
  )
   where

import Data.Profunctor
import Otter.Relation
import qualified Data.Dequeue as D
import qualified Data.Sequence as S
import Data.Foldable

import Debug.Trace

--------------------------------------------------------------------------------

class Subsumable n where
  subsumes :: n -> n -> Bool

--------------------------------------------------------------------------------
-- Types.

data Stage
  = Initial    -- | Initial node
  | Active     -- | Active node
  | Inactive   -- | Inactive node
  | Concl      -- | Conclusion node
  | FSChecked  -- | Forward subsumption-checked
  | BSChecked  -- | Backward subsumption-checked
  | GlIndex    -- | Global index node
  | Goal       -- | Goal node

data SearchNode :: Stage -> * -> * where
  InitN :: seq -> SearchNode Initial seq
  ActiveN :: seq -> SearchNode Active seq
  InactiveN :: seq -> SearchNode Inactive seq
  ConclN :: seq -> SearchNode Concl seq
  FSCheckedN :: seq -> SearchNode FSChecked seq
  BSCheckedN :: seq -> SearchNode BSChecked seq
  GoalN :: seq -> SearchNode Goal seq

deriving instance Show a => Show (SearchNode s a)

extractNode :: SearchNode s seq -> seq
extractNode (InitN s) = s
extractNode (ActiveN s) = s
extractNode (InactiveN s) = s
extractNode (ConclN s) = s
extractNode (BSCheckedN s) = s
extractNode (FSCheckedN s) = s
extractNode (GoalN s) = s

type ActiveNode n = SearchNode Active n
type BSCheckedNode n = SearchNode BSChecked n
type FSCheckedNode n = SearchNode FSChecked n
newtype ActiveNodes n = AS [SearchNode Active n]
type InactiveNode n = SearchNode Inactive n
-- newtype InactiveNodes n = IS (D.BankersDequeue (InactiveNode n))
newtype InactiveNodes n = IS [InactiveNode n]
-- newtype InactiveNodes n = IS (S.Seq (InactiveNode n))

type ConclNode n = SearchNode Concl n
data GlobalIndex n = GI !Int ![n]

instance Foldable GlobalIndex where
  foldr f z (GI _ l) = foldr f z l

--------------------------------------------------------------------------------

initialize :: n -> SearchNode Initial n
initialize = InitN

initIsFSCheckd :: SearchNode Initial n -> FSCheckedNode n
initIsFSCheckd (InitN s) = FSCheckedN s

initIsBSCheckd :: SearchNode Initial n -> BSCheckedNode n
initIsBSCheckd (InitN s) = BSCheckedN s

mkGoal :: n -> SearchNode Goal n
mkGoal = GoalN

emptyActives :: ActiveNodes n
emptyActives = AS mempty

emptyInactives :: InactiveNodes n
emptyInactives = IS mempty
-- emptyInactives = IS [] -- D.empty

emptyGI :: GlobalIndex n
emptyGI = GI 0 mempty

--------------------------------------------------------------------------------

{-| Type of elements that represent the result of applying an inference rule.

    Such application may either fail, succeed with a value (when the rule has
    been fully applied), or succeed with a function (when the rule is only
    partially applied and has still some premises to match). -}
type RuleRes n = Rel (ActiveNode n) (ConclNode n)

{-| Type of inference rules.
    Axioms are not considered rules in this case, so a rule takes at least one
    premise. Hence the corresponding type is a function from a premise sequent
    to a rule application result. -}
type Rule n = ActiveNode n -> RuleRes n

--------------------------------------------------------------------------------
-- Operations

applyRule :: Rule n -> ActiveNode n -> RuleRes n
applyRule = id

foldActives
  :: (forall f. Foldable f => f (ActiveNode n) -> b) -> ActiveNodes n -> b
foldActives folder (AS actives) = folder actives

activate
  :: ActiveNodes n -> InactiveNode n -> (ActiveNodes n, ActiveNode n)
activate (AS as) (InactiveN s) = (AS (ActiveN s : as), ActiveN s)

popInactiveOp
  :: InactiveNodes n -> Maybe (InactiveNodes n, InactiveNode n)
popInactiveOp (IS is) =
  -- case is of
  --   S.Empty -> Nothing
  --   x S.:<| xs -> Just (IS xs, x)
  -- case D.popFront is of
  --   Just (x, xs) -> Just (IS xs, x)
  --   Nothing -> Nothing
  case is of
    (x : xs) -> Just (IS xs, x)
    [] -> Nothing

addToInactives
  :: InactiveNodes n -> GlobalIndex n -> BSCheckedNode n
  -> (InactiveNodes n, GlobalIndex n)
-- addToInactives (IS ins) (GI n gi) (BSCheckedN s) =
--   (IS (ins S.:|> InactiveN s), GI (n + 1) (s : gi))

-- addToInactives (IS ins) (GI n gi) (BSCheckedN s) =
--   (IS (D.pushBack ins (InactiveN s)), GI (n + 1) (s : gi))
-- addToInactives (IS ins) gi (BSCheckedN s) =
--   (IS (InactiveN s : ins), gi)
addToInactives (IS ins) (GI n gi) (BSCheckedN s) =
  (IS (InactiveN s : ins), GI (n + 1) (s : gi))

fwdSubsumes
  :: Subsumable n
  => GlobalIndex n -> SearchNode Concl n -> Maybe (FSCheckedNode n)
fwdSubsumes (GI _ globalIndex) (ConclN s) =
  -- Just (FSCheckedN s)
  if any (`subsumes` s) globalIndex
    then Nothing
    else Just (FSCheckedN s)

removeSubsumedByOp
  :: Subsumable n
  => FSCheckedNode n -> InactiveNodes n -> (InactiveNodes n, BSCheckedNode n)
removeSubsumedByOp (FSCheckedN s) (IS is) =
  -- (IS (S.filter filterer is), BSCheckedN s)
  -- where filterer = not . (s `subsumes`) . extractNode
  -- (IS (D.filterDequeue filterer is), BSCheckedN s)
  -- where filterer = not . (s `subsumes`) . extractNode
  let ff = filter filterer is
  in (IS ff, BSCheckedN s) -- traceShow (length ff) (IS ff, BSCheckedN s)
  where filterer = not . (s `subsumes`) . extractNode

toProverRules :: (n -> Rel n n) -> Rule n
toProverRules = dimap extractNode (dimap extractNode ConclN)
