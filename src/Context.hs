{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Context
  ( module Data.Semigroup
  , Context(..)
  , SubCtxt(..)
  , fromFoldable
  , subCtxtOfBool
  ) where

import Utils ((.:))
import qualified Data.List.NonEmpty as NE
import Control.Monad.Fail
import Data.Constraint
import Data.Semigroup
import TypeClasses (CanMap, EqInfo(..), Eq'(..))
import Data.Bifunctor (bimap)

--------------------------------------------------------------------------------
-- Context class

data SubCtxt elem = SC
  { scOnOnlyFirst :: [elem]
  , scRestFirst :: [elem]
  }

-- | Typeclass of generic contexts to be used in sequents and during
-- proof-search.
class Semigroup ctxt => Context ctxt where
  type Elems ctxt :: *
  -- | Add an element to the context.
  add :: Elems ctxt -> ctxt -> ctxt
  singleton :: Elems ctxt -> ctxt
  -- | Returns a list of elements of the first context in case it is not a
  -- subcontext of the second.
  subCtxtOf :: Context ctxt => ctxt -> ctxt -> SubCtxt (Elems ctxt)
  asFoldable :: (forall f. Foldable f => f (Elems ctxt) -> b) -> ctxt -> b

subCtxtOfBool :: Context ctxt => ctxt -> ctxt -> Bool
subCtxtOfBool = null . scOnOnlyFirst .: subCtxtOf

fromFoldable
  :: (Monoid ctxt, Context ctxt, Foldable f)
  => f (Elems ctxt) -> ctxt
fromFoldable f = foldr add mempty f
