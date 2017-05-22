{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

module LinearContext
  ( Context(..)
  , module Context
  , LinearCtxt
  , subCtxtOf
  ) where

import Data.List (intersperse)
import Control.Monad hiding (fail)
import Data.Maybe (fromMaybe)
import Data.Semigroup
import Data.Foldable
import qualified Data.Map as M
import Control.Monad.Fail
import Prelude hiding (fail)
import Context
import qualified TypeClasses as T (CanMap(..), Pretty(..))

--------------------------------------------------------------------------------
-- Helper numeric datatype

-- | Type of positive natural numbers (hence excluding zero).
-- data PosNat = One | Succ PosNat deriving (Eq, Show)

-- instance Semigroup PosNat where
--   One <> m = Succ m
--   Succ n <> m = Succ (n <> m)

-- instance Ord PosNat where
--   compare pn1 pn2 = compare (toNum pn1 :: Int) (toNum pn2)

-- toNum :: Num t => PosNat -> t
-- toNum One = 1
-- toNum (Succ n) = toNum n + 1

-- minusOne :: PosNat -> Maybe PosNat
-- minusOne One = Nothing
-- minusOne (Succ n) = Just n

-- repeatPN :: a -> PosNat -> NE.NonEmpty a
-- repeatPN x One = x NE.:| []
-- repeatPN x (Succ n) = (x NE.:| []) <> repeatPN x n

repeatN :: a -> Int -> [a]
repeatN x i = take i $ repeat x

minusOne :: Int -> Maybe Int
minusOne 1 = Nothing
minusOne n | n > 1 = Just (n - 1)
           | otherwise = error "invalid non-positive integer"

--------------------------------------------------------------------------------

newtype LinearCtxt a = LC (M.Map a Int) deriving (Eq, Ord, Show)

instance Foldable LinearCtxt where
  foldr f z (LC lc) = foldr f z listed
    where
      listed = M.foldMapWithKey (\x y -> repeatN x y) lc

subCtxtOf :: (Eq a, Ord a) => LinearCtxt a -> LinearCtxt a -> Bool
subCtxtOf (LC m1) (LC m2) =
  if m1 == m2
    then True
    else and $ map duane (M.toList m1)
  where
    duane (key, val) = fromMaybe False $ M.lookup key m2 >>= return . (val <=)

instance Ord a => Monoid (LinearCtxt a) where
  mempty = LC M.empty
  (LC map1) `mappend` (LC map2) = LC $ M.unionWith (+) map1 map2

instance (Ord a) => Context (LinearCtxt a) where
  type Elems (LinearCtxt a) = a
  add x (LC lc) = LC (M.insertWith (+) x 1 lc)
  removeM x (LC lc) = if M.member x lc
                         then return . LC $ M.update minusOne x lc
                         else fail "element not in context"
  asFoldable f lc = f lc

instance T.Pretty a => T.Pretty (LinearCtxt a) where
  pretty (LC m) = concat . intersperse "," . map T.pretty . M.keys $ m

instance T.CanMap LinearCtxt where
  type Constr LinearCtxt x = Ord x
  map f (LC m) = LC (M.mapKeys f m)
