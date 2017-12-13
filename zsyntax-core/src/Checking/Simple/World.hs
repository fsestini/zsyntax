{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Checking.Simple.World where

import qualified Data.Set as S
import Formula
import Checking
import SFormula
import Data.Monoid ((<>))
import Control.Monad.Reader.Class
import Control.Monad (liftM2, mapM)
import LinearContext
import Data.Foldable

newtype CtrlSet a = CS (S.Set (BioFormula a))
newtype ElemBase a = EB (S.Set (BioFormula a)) deriving (Monoid)

data World a = W { infoMap :: SFormula a -> SFormula a -> S.Set (ElemBase a, CtrlSet a) }

data WorldInstance a = WI
  { baseMap :: SFormula a -> SFormula a -> ElemBase a
  , ctrlMap :: SFormula a -> SFormula a -> CtrlSet a
  }

formulaBase
  :: (Ord a, MonadReader (WorldInstance a) m)
  => SFormula a -> m (ElemBase a)
formulaBase (SAtom atom) = return $ EB $ S.singleton atom
formulaBase (SConj f1 f2) = liftM2 (<>) (formulaBase f1) (formulaBase f2)
formulaBase (SImpl f1 f2) = do
  w <- ask
  return $ baseMap w f1 f2

computeBase
  :: (Ord a, MonadReader (WorldInstance a) m, Monad m)
  => LinearCtxt (SFormula a) -> m (ElemBase a)
computeBase = fmap (foldr (<>) mempty) . mapM formulaBase . toList
