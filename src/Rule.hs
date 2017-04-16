{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Rule where

import Formula
import LabelledSequent
import Relation
import Rel

{-| Type of elements that represent the result of applying an inference rule.

    Such application may either fail, succeed with a value (when the rule has
    been fully applied), or succeed with a function (when the rule is only
    partially applied and has still some premises to match). -}
type RuleRes l a = Rel (LabelledSequent l a) (LabelledSequent l a)

{-| Type of inference rules.
    Axioms are not considered rules in this case, so a rule takes at least one
    premise. Hence the corresponding type is a function from a premise sequent
    to a rule application result. -}
type Rule l a = (LabelledSequent l a) -> RuleRes l a

-- genRule
--   :: (Eq a, Eq l)
--   => DecLFormula l a -> Rule l a
-- genRule (UnrestrDLF formula) = do
--   (MRes gamma delta (LabelResult goal)) <- negativeFocalDispatch formula
--   return $ LS (addToUnrestrCtxt (label formula) gamma) delta goal
-- genRule (LinearNegativeDLF formula) = do
--   (MRes gamma delta (LabelResult goal)) <- negativeFocalDispatch formula
--   return $ LS gamma (addToLinCtxt (label formula) delta) goal
-- genRule (LinearPositiveDLF formula) = do
--   (MRes gamma delta _) <- positiveFocalDispatch formula
--   return $ LS gamma delta (label formula)
  
-- TODO !!!!!!!!!!!

-- Prove that there is no risk that a rule is inserted in the rule pool more
-- than once, and so we do not need to compare rules for equality.  Intuitively,
-- it should be possible to prove that the search loop makes sure that every
-- rule is applied to a particular sequent at most once in the same "premise"
-- position.

-------------------
