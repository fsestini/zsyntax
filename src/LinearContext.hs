{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

module LinearContext
  ( Context(..)
  , singletonCtxt
  , LinearCtxt
  , subCtxtOf
  ) where

import Data.List (intersperse)
import Control.Monad hiding (fail)
import Data.Maybe (fromMaybe)
import Data.Semigroup
import Data.Foldable
import qualified Data.Map as M
import qualified Data.List.NonEmpty as NE
import Control.Monad.Fail
import Prelude hiding (fail)
import Context

--------------------------------------------------------------------------------
-- Helper numeric datatype

-- | Type of positive natural numbers (hence excluding zero).
data PosNat = One | Succ PosNat deriving (Eq, Show)

instance Semigroup PosNat where
  One <> m = Succ m
  Succ n <> m = Succ (n <> m)

instance Ord PosNat where
  compare pn1 pn2 = compare (toNum pn1 :: Int) (toNum pn2)

toNum :: Num t => PosNat -> t
toNum One = 1
toNum (Succ n) = toNum n + 1

minusOne :: PosNat -> Maybe PosNat
minusOne One = Nothing
minusOne (Succ n) = Just n

repeatPN :: a -> PosNat -> NE.NonEmpty a
repeatPN x One = x NE.:| []
repeatPN x (Succ n) = (x NE.:| []) <> repeatPN x n

--------------------------------------------------------------------------------

newtype LinearCtxt a = LC (M.Map a PosNat) deriving (Eq, Ord)

instance Foldable LinearCtxt where
  foldr f z (LC lc) = foldr f z listed
    where
      listed = M.foldMapWithKey (\x y -> NE.toList (repeatPN x y)) lc

subCtxtOf :: (Eq a, Ord a) => LinearCtxt a -> LinearCtxt a -> Bool
subCtxtOf (LC m1) (LC m2) =
  if m1 == m2
    then True
    else and $ map duane (M.toList m1)
  where
    duane (key, val) = fromMaybe False $ M.lookup key m2 >>= return . (val <)

instance Ord a => Monoid (LinearCtxt a) where
  mempty = LC M.empty
  (LC map1) `mappend` (LC map2) = LC $ M.unionWith (<>) map1 map2

instance (Ord a) => Context (LinearCtxt a) a where
  add x (LC lc) = LC (M.insertWith (<>) x One lc)
  removeM x (LC lc) = if M.member x lc
                         then return . LC $ M.update minusOne x lc
                         else fail "element not in context"
  asFoldable f lc = f lc

instance Show a => Show (LinearCtxt a) where
  show (LC m) = concat . intersperse "," . map show . M.keys $ m
