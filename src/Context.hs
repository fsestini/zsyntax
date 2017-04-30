{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Context where

import Control.Monad.Fail

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

fromFoldable :: (Foldable f, Monoid ctxt, Context ctxt elems) => f (elems) -> ctxt
fromFoldable = foldr add mempty

singletonCtxt :: (Monoid ctxt, Context ctxt elems) => elems -> ctxt
singletonCtxt x = add x mempty
