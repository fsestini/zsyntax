{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Context
  ( module Data.Semigroup
  , Context(..)
  , fromFoldable
  , subCtxtOfBool
  ) where

import qualified Data.List.NonEmpty as NE
import Control.Monad.Fail
import Data.Constraint
import Data.Semigroup
import TypeClasses (CanMap)
import Data.Bifunctor (bimap)

--------------------------------------------------------------------------------
-- Context class

-- | Typeclass of generic contexts to be used in sequents and during
-- proof-search.
class Semigroup ctxt => Context ctxt where
  type Elems ctxt :: *
  -- | Add an element to the context.
  add :: Elems ctxt -> ctxt -> ctxt
  singleton :: Elems ctxt -> ctxt
  -- | Returns a list of elements of the first context in case it is not a
  -- subcontext of the second.
  subCtxtOf :: ctxt -> ctxt -> [Elems ctxt]
  -- | Equality comparison function that returns a proof in the case the two
  -- contexts are different. The proof is a pair containing a list of elements of
  -- the first contexts that are missing from the second, and a list of elements
  -- of the second that are missing from the first.
  -- The two contexts are equal iff the two lists are both empty.
  eqCtxt :: ctxt -> ctxt -> ([Elems ctxt],[Elems ctxt])
  eqCtxt c1 c2 = (c1 `subCtxtOf` c2, c2 `subCtxtOf` c1)
  asFoldable :: (forall f. Foldable f => f (Elems ctxt) -> b) -> ctxt -> b

subCtxtOfBool :: Context ctxt => ctxt -> ctxt -> Bool
subCtxtOfBool c1 c2 = null (subCtxtOf c1 c2)

fromFoldable
  :: (Monoid ctxt, Context ctxt, Foldable f)
  => f (Elems ctxt) -> ctxt
fromFoldable f = foldr add mempty f

maybeEqCtxt
  :: Context ctxt
  => ctxt
  -> ctxt
  -> (Maybe (NE.NonEmpty (Elems ctxt)), Maybe (NE.NonEmpty (Elems ctxt)))
maybeEqCtxt c1 c2 = bimap NE.nonEmpty NE.nonEmpty (eqCtxt c1 c2)
