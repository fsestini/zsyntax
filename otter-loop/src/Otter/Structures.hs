{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}

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
  , SearchRule
  , SearchProperRule
  , Subsumable(..)
  -- , OrdSearchGoal(..)
  -- , applyRule
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
  , toProperRule
  , extractNode
  )
   where

import Otter.Relation

class Subsumable n where
  subsumes :: n -> n -> Bool

data Stage
  = Initial    -- ^ Initial node
  | Active     -- ^ Active node
  | Inactive   -- ^ Inactive node
  | Concl      -- ^ Conclusion node
  | FSChecked  -- ^ Forward subsumption-checked
  | BSChecked  -- ^ Backward subsumption-checked
  | GlIndex    -- ^ Global index node
  | Goal       -- ^ Goal node

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
newtype InactiveNodes n = IS [InactiveNode n]

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

emptyGI :: GlobalIndex n
emptyGI = GI 0 mempty

--------------------------------------------------------------------------------

{-| Type of elements that represent the result of applying an inference rule.

    Such application may either fail, succeed with a value (when the rule has
    been fully applied), or succeed with a function (when the rule is only
    partially applied and has still some premises to match). -}
type SearchRule n = Rule (ActiveNode n) (ConclNode n)

{-| Type of inference rules.
    Axioms are not considered rules in this case, so a rule takes at least one
    premise. Hence the corresponding type is a function from a premise sequent
    to a rule application result. -}
type SearchProperRule n = ProperRule (ActiveNode n) (ConclNode n)

toProperRule :: (n -> Rule n n) -> SearchProperRule n
toProperRule = arrowDimap extractNode (relDimap extractNode ConclN)

--------------------------------------------------------------------------------
-- Operations

foldActives
  :: (forall f. Foldable f => f (ActiveNode n) -> b) -> ActiveNodes n -> b
foldActives folder (AS actives) = folder actives

activate
  :: ActiveNodes n -> InactiveNode n -> (ActiveNodes n, ActiveNode n)
activate (AS as) (InactiveN s) = (AS (ActiveN s : as), ActiveN s)

popInactiveOp
  :: InactiveNodes n -> Maybe (InactiveNodes n, InactiveNode n)
popInactiveOp (IS is) =
  case is of
    (x : xs) -> Just (IS xs, x)
    [] -> Nothing

addToInactives
  :: InactiveNodes n -> GlobalIndex n -> BSCheckedNode n
  -> (InactiveNodes n, GlobalIndex n)
addToInactives (IS ins) (GI n gi) (BSCheckedN s) =
  (IS (InactiveN s : ins), GI (n + 1) (s : gi))

fwdSubsumes
  :: Subsumable n
  => GlobalIndex n -> SearchNode Concl n -> Maybe (FSCheckedNode n)
fwdSubsumes (GI _ globalIndex) (ConclN s) =
  if any (`subsumes` s) globalIndex
    then Nothing
    else Just (FSCheckedN s)

removeSubsumedByOp
  :: Subsumable n
  => FSCheckedNode n -> InactiveNodes n -> (InactiveNodes n, BSCheckedNode n)
removeSubsumedByOp (FSCheckedN s) (IS is) =
  let ff = filter filterer is
  in (IS ff, BSCheckedN s)
  where filterer = not . (s `subsumes`) . extractNode
