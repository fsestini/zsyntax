{-# LANGUAGE GeneralizedNewtypeDeriving, DerivingStrategies, OverloadedStrings #-}

-- | Benchmarks for Zsyntax

module Main where

import Zsyntax
import Zsyntax.Labelled.Formula
import qualified Otter as O
import System.Exit (exitFailure)
import qualified Data.Set as S (fromList)
import qualified Data.MultiSet as M
import Data.List.NonEmpty (fromList)
import Zsyntax.ReactionList
import Data.Text (Text, pack)

import Criterion
import Criterion.Main (defaultMain)
import Data.String (IsString)

newtype BioLabel = BioLabel Text deriving newtype (Eq, Ord, Show, IsString)

main :: IO ()
main =
  defaultMain
    [ bgroup "proof search test"
      [ bench "search" $ whnf checkSequent goal
      ]
    ]

-- boundedSearch :: Sequent a -> Extraction (Decora)
-- boundedSearch = O.extractResults 2000 . fst . search . toLabelledGoal

checkSequent :: Ord a => Sequent a -> Bool -- IO ()
checkSequent g =
  case otterResult (search g 5000) of -- (toLabelledGoal g)) of
    Right _ -> True -- putStrLn "test passed."
    Left _  -> False -- putStrLn "test failed." >> exitFailure

ax :: Ord a => [a] -> [a] -> [a] -> Axiom (BioFormula a)
ax xs ys rl =
  axiom (fromList $ fmap BioAtom xs)
        (justCS $ fromCSCtxts [CSC SupersetClosed
                                (M.fromList (fmap BioAtom rl))])
        (fromList $ fmap BioAtom ys)

type Atom = BioFormula String

goal :: Sequent Atom
goal = SQ (S.fromList axioms) (M.fromList from) to
  where
    axioms :: [Axiom Atom]
    axioms =
      [ ax ["A"] ["A,A"] mempty
      , ax ["A,A"] ["B"] mempty
      , ax ["B,B"] ["C"] mempty
      , ax ["C,C"] ["D"] mempty
      , ax ["D,D"] ["E"] mempty
      , ax ["E,E"] ["F"] mempty
      , ax ["F,F"] ["G"] mempty
      , ax ["H,H"] ["I"] mempty
      , ax ["I,I"] ["L"] mempty
      , ax ["L,L"] ["M"] mempty
      , ax ["M,M"] ["N"] mempty
      ]
    from :: [Formula Atom]
    from = [atom (BioAtom "A")]
    to :: Formula Atom
    to = foldr1 conj (replicate 1000 (atom (BioAtom "N")))
