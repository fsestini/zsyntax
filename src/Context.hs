{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Context
  ( module Data.Semigroup
  , Context(..)
  , fromFoldable
  ) where

import Control.Monad.Fail
import Data.Constraint
import Data.Semigroup
import TypeClasses (CanMap)

--------------------------------------------------------------------------------
-- Context class

-- | Typeclass of generic contexts to be used in sequents and during
-- proof-search.
class Semigroup ctxt => Context ctxt where
  type Elems ctxt :: *
  -- | Add an element to the context.
  add :: Elems ctxt -> ctxt -> ctxt
  singleton :: Elems ctxt -> ctxt
  subCtxtOf :: ctxt -> ctxt -> Bool
  asFoldable
    :: (forall f. Foldable f =>
                    f (Elems ctxt) -> b)
    -> ctxt
    -> b

fromFoldable
  :: (Monoid ctxt, Context ctxt, Foldable f)
  => f (Elems ctxt) -> ctxt
fromFoldable f = foldr add mempty f
