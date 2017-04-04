{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Rule where

import Formula
import Relation

type Rule l a = (LabelledSequent l a) -> RuleRes l a

type RuleRes l a = Rel (LabelledSequent l a) (LabelledSequent l a)

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
