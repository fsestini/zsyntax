{-# LANGUAGE TypeOperators #-}

module Zsyntax
  ( module Zsyntax.Formula
  , search
  , toLabelledGoal
  , O.SearchRes
  , O.Extraction(..)
  , O.FailureReason(..)
  , O.extractResults
  ) where

import qualified Otter as O
import Zsyntax.Formula
import Zsyntax.Labelled.Rule.Interface
import Zsyntax.Labelled.Rule
import Zsyntax.Labelled.DerivationTerm
import Data.Foldable
import Control.Monad.State
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Bifunctor (bimap)
import qualified Data.Map.Strict as M
import Data.Tuple (swap)

type DecoratedLSequent a l = DerivationTerm a l ::: LSequent a l

toLabelledGoal :: Ord a => Sequent a -> GoalNSequent a Int
toLabelledGoal s = evalState (neutralize s) 0

search :: Ord a
       => Sequent a
       -> (O.SearchRes (DecoratedLSequent a Int) , [DecoratedLSequent a Int])
search s = bimap (map (fmap mapDLS)) (map mapDLS) res
  where
    (s', m) = countAtoms s
    res = search' (toLabelledGoal s')
    mMap = M.fromList . map swap . M.toAscList $ m
    mFun x = fromMaybe (error "error in generating IntAtom map") (M.lookup x mMap)
    mapDLS = bimap (mapDerivationTerm mFun) (mapLSequent mFun)

search' :: GoalNSequent IntAtom Int
       -> ( O.SearchRes (DecoratedLSequent IntAtom Int)
          , [DecoratedLSequent IntAtom Int])
search' goal = O.search (toList seqs) rules isGoal
  where
    initial = initialRules goal
    seqs    = mapMaybe maySequent initial
    rules   = mapMaybe mayProperRule initial
    isGoal s' = (toGoalSequent . _payload $ s') `O.subsumes` goal
