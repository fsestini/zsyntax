{-# LANGUAGE DeriveFunctor #-}

module Otter.SearchRes
  ( SearchRes
  , Res(..)
  , Extraction(..)
  , FailureReason(..)
  , extractResults
  , delay
  , cons
  ) where

import Data.List.NonEmpty (NonEmpty(..))

data Res a = Res a | Delay deriving (Functor)

-- | Type representing the result of proof search. Every element in the list
-- corresponds to the result of analysing node in the search space by the search
-- algorithm. The result is 'Res' in the positive case the node is a goal node,
-- or 'Delay' in the negative case.
--
-- The search agorithm produces an element of `'SearchRes' a` lazily, inserting
-- 'Delay' constructors to ensure that the computation is productive even in the
-- case no goal node is found in the search space. This allows to perform proof
-- search in an on-demand fashion, possibly giving up after a certain number of
-- 'Delay's.
type SearchRes a = [Res a]

-- | Delays a search result stream.
--
-- @
-- delay x == Delay : x
-- @
delay :: SearchRes a -> SearchRes a
delay = (Delay :)

-- | Appends a result to a search result stream.
--
-- @
-- cons x y = Res x : y
-- @
cons :: a -> SearchRes a -> SearchRes a
cons x = (Res x :)

-- | Type of reasons why no result can be extracted from a search result stream.
-- 
-- Either the search space has been exhaustively searched and no result was
-- found (the query is not a theorem), or the search was terminated preemptively
-- according to an upper bound imposed on the maximum depth of the search space.
data FailureReason = NotATheorem | SpaceTooBig

-- | Type of the result of 'extractResults', which extracts all positive search
-- results from a search result stream.
-- An element of `Extraction a` is either a non-empty list of positive results,
-- or an element of 'SpaceExhausted' giving a reason why no result was found.
data Extraction a = AllResults (NonEmpty a) | NoResults FailureReason

resListUntil :: Int -> SearchRes a -> ([a], FailureReason)
resListUntil _ [] = ([], NotATheorem)
resListUntil 0 (_ : _)  = ([], SpaceTooBig)
resListUntil i (Res x : xs) = let (ys, b) = resListUntil i xs in (x : ys, b)
resListUntil i (Delay : xs) = resListUntil (i - 1) xs

-- | Extract all the positive results from a search result stream, stopping if
-- no result is found after the given number of delays.
extractResults :: Int -> SearchRes a -> Extraction a
extractResults i res = case resListUntil i res of
  ([], b) -> NoResults b
  (x : xs, _) -> AllResults (x :| xs)
  
