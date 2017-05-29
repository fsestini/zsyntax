{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module UnrestrContext
  ( module Context
  , UnrestrCtxt
  ) where

import qualified Data.Set as S
import Context
import Data.Semigroup
import Data.List (intersperse)
import qualified TypeClasses as T

newtype UnrestrCtxt a = UC (S.Set a) deriving (Eq, Ord, Monoid, Semigroup)

instance Foldable UnrestrCtxt where
  foldr f z (UC set) = foldr f z set

instance Ord a => Context (UnrestrCtxt a) where
  type Elems (UnrestrCtxt a) = a
  add x (UC set) = UC (S.insert x set)
  singleton x = UC (S.singleton x)
  subCtxtOf (UC s1) (UC s2) = S.isSubsetOf s1 s2
  asFoldable f (UC set) = f set

instance Show a => Show (UnrestrCtxt a) where
  show (UC uc) = concat $ intersperse "," (map show (S.toList uc))

instance T.CanMap UnrestrCtxt where
  type Constr UnrestrCtxt x = Ord x
  map f (UC s) = UC . S.fromList . map f . S.toList $ s
