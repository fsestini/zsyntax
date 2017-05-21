{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Context where

import Control.Monad.Fail

--------------------------------------------------------------------------------
-- Context class

class Monoid ctxt => Context ctxt where
  type Elems ctxt :: *
  add :: Elems ctxt -> ctxt -> ctxt
  removeM :: MonadFail m => Elems ctxt -> ctxt -> m ctxt
  asFoldable :: (forall f . Foldable f => f (Elems ctxt) -> b) -> ctxt -> b
  remove :: Elems ctxt -> ctxt -> ctxt
  remove x c = case removeM x c of
                 Just c' -> c'
                 Nothing -> error "element not in context"

fromFoldable :: (Foldable f, Context ctxt) => f (Elems ctxt) -> ctxt
fromFoldable = foldr add mempty

singletonCtxt :: (Context ctxt) => Elems ctxt -> ctxt
singletonCtxt x = add x mempty
