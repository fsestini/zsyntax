{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module LinearContext where

import Data.Semigroup
import qualified Data.Map as M
import qualified Data.List.NonEmpty as NE
import Control.Monad.Fail
import Prelude hiding (fail)

--------------------------------------------------------------------------------
-- Context class

class Context ctxt elems where
  add :: elems -> ctxt -> ctxt
  removeM :: MonadFail m => elems -> ctxt -> m ctxt
  asFoldable :: (forall f . Foldable f => f (elems) -> b) -> ctxt -> b
  remove :: elems -> ctxt -> ctxt
  remove x c = case removeM x c of
                 Just c' -> c'
                 Nothing -> error "element not in context"

--------------------------------------------------------------------------------
-- Numeric datatypes

data Nat = Zero | NatSucc Nat

-- | Type of positive natural numbers (hence excluding zero).
data PosNat = One | Succ PosNat deriving (Eq, Show)

instance Semigroup PosNat where
  One <> m = Succ m
  Succ n <> m = Succ (n <> m)

neLength :: NE.NonEmpty a -> PosNat
neLength = sconcat . fmap (const One)

minusOne :: PosNat -> Maybe PosNat
minusOne One = Nothing
minusOne (Succ n) = Just n

repeatPN :: a -> PosNat -> NE.NonEmpty a
repeatPN x One = x NE.:| []
repeatPN x (Succ n) = undefined

newtype LinearCtxt a = LC (M.Map a PosNat) deriving (Eq)

instance Ord a => Monoid (LinearCtxt a) where
  mempty = LC M.empty
  (LC map1) `mappend` (LC map2) = LC $ M.unionWith (<>) map1 map2

instance (Ord a) => Context (LinearCtxt a) a where
  add x (LC lc) = LC (M.insertWith (<>) x One lc)
  removeM x (LC lc) = if M.member x lc
                         then return . LC $ M.update minusOne x lc
                         else fail "element not in context"
  asFoldable f (LC lc) = f listed
    where
      listed = M.foldMapWithKey (\x y -> NE.toList (repeatPN x y)) lc
