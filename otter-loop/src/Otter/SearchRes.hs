{-# LANGUAGE DeriveFunctor #-}

module Otter.SearchRes
  ( SearchRes
  , ExtractionRes(..)
  , resListUntil
  , delay
  , cons
  ) where

-- import Data.Bifunctor

-- interleave :: [a] -> [a] -> [a]
-- interleave xs ys = (concat . transpose) [xs, ys]

data Res a = Res a | Delay deriving (Functor)
type SearchRes a = [Res a]

delay :: SearchRes a -> SearchRes a
delay = (Delay :)

cons :: a -> SearchRes a -> SearchRes a
cons x = (Res x :)

data ExtractionRes a = ExtractionRes
  { _erResult :: [a]
  , _erSpaceExhausted :: Bool
  }

-- | Extract the list of results, but stop and return with failure
-- in case no result is found after the given number of delays.
resListUntil :: Int -> SearchRes a -> ExtractionRes a -- Either [a] [a]
resListUntil _ [] = ExtractionRes [] True -- Right []
resListUntil 0 (_ : _)  = ExtractionRes [] False -- Left []
resListUntil i (Res x : xs) =
  let y = resListUntil i xs in y { _erResult = x : _erResult y }
  -- bimap (x:) (x:) (resListUntil i xs)
resListUntil i (Delay : xs) = resListUntil (i - 1) xs
