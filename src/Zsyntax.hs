{-# LANGUAGE TypeOperators #-}

module Zsyntax
  ( module Zsyntax.Formula
  , search
  , toLabelledGoal
  , O.SearchRes
  , O.ExtractionRes(..)
  , O.resListUntil
  ) where

import qualified Otter as O
import Zsyntax.Formula
import Zsyntax.Labelled.Rule.Interface
import Zsyntax.Labelled.Rule
import Zsyntax.Labelled.DerivationTerm
import Data.Foldable
import Control.Monad.State
import Data.Maybe (mapMaybe)

type DecoratedLSequent a l = DerivationTerm a l ::: LSequent a l

toLabelledGoal :: Ord a => Sequent a -> GoalNSequent a Int
toLabelledGoal s = evalState (neutralize s) 0

search :: Ord a
       => GoalNSequent a Int
       -> ( O.SearchRes (DecoratedLSequent a Int)
          , [DecoratedLSequent a Int])
search goal = O.search (toList seqs) rules isGoal
  where
    initial = initialRules goal
    seqs    = mapMaybe maySequent initial
    rules   = mapMaybe mayProperRule initial
    isGoal s' = (toGoalSequent . _payload $ s') `O.subsumes` goal
