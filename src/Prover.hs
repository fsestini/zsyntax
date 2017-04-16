{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

module Prover where


import Control.Arrow
import Formula
import LabelledSequent
import Rule
import qualified Data.Set as S
import qualified Data.Map as M
import Filterable
import Relation
import Rel
import Prover.Class
import Prover.Transformer

-- TODO: use the real thing
type DerivationTerm l a = Int

processNewActive
  :: (Monad m, HasProverState l a m)
  => LabelledSequent l a -> m (RuleAppRes l a)
processNewActive sequent = do
  actives <- getActives
  rules <- getRules
  let r1 = applyAll rules sequent
      r2 = percolate actives . resRules $ r1
  return $ r1 `mappend` r2

{-

  1. Compute frontier
  2. Compute initial set of rules ---> initial sequents
  3. Put initial sequents in inactive set
  4. Pop inactive sequent. If no more, goto
  5. Put popped inactive in active set
  6. Apply all rules to sequent
  7. Percolate
  8. Add resulting sequents that are not subsumed by old inactive sequents to
     inactive set
  9. Remove inactive sequents that are subsumed by the new sequents
  10. Add rules to rule set
  11. Is any new sequent subsumed the goal, exit
  12. Add new sequents to inactive set
  13. Goto 4

-}

otterLoop
  :: (Monad m, HasProverState l a m, HasProverEnvironment l a m)
  => m (Maybe (DerivationTerm l a))
otterLoop = do
  -- TODO!!! check here if any inactive sequent subsumes the goal sequent
  inactive <- popInactive
  case inactive of
    Nothing -> return Nothing
    Just sequent -> do
      addActive sequent
      (seqs, rules) <- processNewActive sequent
      unsubSeqs <- filterUnsubsumed seqs
      addInactives unsubSeqs
      addRules rules
      return (Just sequent)
