{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module UnrestrContext where

import qualified Data.Set as S
import Context
import Data.List (intersperse)
import qualified TypeClasses as T

newtype UnrestrCtxt a = UC (S.Set a) deriving (Eq, Ord, Monoid)

instance Ord a => Context (UnrestrCtxt a) a where
  add x (UC set) = UC (S.insert x set)
  removeM x (UC set) = if S.member x set
                          then return . UC $ S.delete x set
                          else fail "element not in context"
  asFoldable f (UC set) = f set

instance Show a => Show (UnrestrCtxt a) where
  show (UC uc) = concat $ intersperse "," (map show (S.toList uc))

instance T.CanMap UnrestrCtxt where
  type Constr UnrestrCtxt x = Ord x
  map f (UC s) = UC . S.fromList . map f . S.toList $ s
