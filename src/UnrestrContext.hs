{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module UnrestrContext where

import qualified Data.Set as S
import Context

newtype UnrestrCtxt a = UC (S.Set a) deriving (Eq, Ord, Monoid, Show)

instance Ord a => Context (UnrestrCtxt a) a where
  add x (UC set) = UC (S.insert x set)
  removeM x (UC set) = if S.member x set
                          then return . UC $ S.delete x set
                          else fail "element not in context"
  asFoldable f (UC set) = f set
