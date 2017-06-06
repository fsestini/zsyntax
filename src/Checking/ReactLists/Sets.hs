{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Checking.ReactLists.Sets
  ( ElemBase
  , CtrlSet
  , fromFoldableCtxts
  , toCtxtList
  , CtrlSetCtxt(..)
  , asFoldable
  ) where

import SFormula (BioFormula(..))
import LFormula (SrchFormula(..))
import Rules
import LinearContext
import qualified Data.Set as S
import Data.Foldable (toList)

{-| A control set is a set of linear contexts made up of atomic formulas, that is,
    multisets of formulas of the bonding language.

    For a context C in a control set S we may want to consider its superset
    closure, that is, have that C' is in S for all superset C' of C.
    We therefore distinguish between superset-closed contexts and normal
    contexts in a control set. Actually, superset-closed contexts are the only
    way to specify infinite control sets. -}

data CtrlSetCtxt a = Regular (NonEmptyLinearCtxt (BioFormula a))
                   | SupsetClosed (NonEmptyLinearCtxt (BioFormula a))
                   deriving (Eq, Ord, Show)
newtype CtrlSet a = CS
  { unCS :: S.Set (CtrlSetCtxt a)
  } deriving (Eq, Ord, Monoid, Show)
newtype ElemBase a = EB
  { unEB :: LinearCtxt (BioFormula a)
  } deriving (Eq, Ord, Monoid, Semigroup, Show)

fromFoldableCtxts :: (Ord a, Foldable f) => f (CtrlSetCtxt a) -> CtrlSet a
fromFoldableCtxts = CS . S.fromList . toList

toCtxtList :: CtrlSet a -> [CtrlSetCtxt a]
toCtxtList = S.toList . unCS

respectsCtrlSet :: (Ord a, Eq a) => ElemBase a -> CtrlSet a -> Bool
respectsCtrlSet f = and . S.map (respectsCtrlCtxt f) . unCS

respectsCtrlCtxt :: (Eq a, Ord a) => ElemBase a -> CtrlSetCtxt a -> Bool
respectsCtrlCtxt (EB base) (Regular ctxt) = not (base == (toLC ctxt))
respectsCtrlCtxt (EB base) (SupsetClosed ctxt) = not ((toLC ctxt) `subCtxtOf` base)

instance (Ord a, Ord l) => HasElemBase (SrchFormula (ElemBase a) cty a l) where
  formulaBase (switchF' -> T1 (AR x _)) = EB (singleton x)
  formulaBase (switchF' -> T2 (CR f1 f2 _)) = formulaBase f1 <> formulaBase f2
  formulaBase (switchF' -> T3 (IR _ eb _ _ _)) = eb

instance Ord a => BaseCtrl (ElemBase a) (CtrlSet a) where
  respects = respectsCtrlSet
