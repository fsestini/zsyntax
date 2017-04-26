{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Checking.ConstrCtxt
  ( ConstrCtxt
  , singleton
  , add
  , remove
  , labels
  , schemaOf
  ) where

import qualified LabelledSequent as L
import Formula
import Checking.ControlSet
import Control.Monad.Fail
import qualified Data.Map as M

newtype ConstrCtxt l a =
  CC (M.Map (Label l a) (BCSchema l a), L.LinearCtxt l a)
  deriving (Monoid)

singleton :: Label l a -> BCSchema l a -> ConstrCtxt l a
singleton lbl bs = CC (M.singleton lbl bs, L.singletonLinearCtxt lbl)

add
  :: (Ord l, Ord a)
  => Label l a
  -> BCSchema l a
  -> ConstrCtxt l a
  -> ConstrCtxt l a
add lbl bs c = singleton lbl bs `mappend` c

schemaOf
  :: (Ord a, Ord l)
  => ConstrCtxt l a -> Label l a -> BCSchema l a
schemaOf (CC (m, _)) lbl = case (M.lookup lbl m) of
  Just bs -> bs
  Nothing -> error "no label in context"

remove
  :: (MonadFail m, Ord l, Ord a)
  => Label l a -> ConstrCtxt l a -> m (ConstrCtxt l a)
remove lbl (CC (m1, m2)) = do
  newLC <- L.remove lbl m2
  return $ CC (M.delete lbl m1, newLC)

labels :: ConstrCtxt l a -> [Label l a]
labels (CC (m, _)) = M.keys m
