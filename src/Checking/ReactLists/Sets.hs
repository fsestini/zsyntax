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
  ) where

import qualified RelFormula as F
       (BioFormula, ElemBase(..), ControlSet(..), BaseCtrl(..),
        LFormula(..), ImplFormula(..))
import LinearContext
import qualified Data.Set as S
import Data.Monoid ((<>))
import Data.Foldable (toList)

{-| A control set is a set of linear contexts made up of atomic formulas, that is,
    multisets of formulas of the bonding language.

    For a context C in a control set S we may want to consider its superset
    closure, that is, have that C' is in S for all superset C' of C.
    We therefore distinguish between superset-closed contexts and normal
    contexts in a control set. Actually, superset-closed contexts are the only
    way to specify infinite control sets. -}

data CtrlSetCtxt a = Regular (LinearCtxt (F.BioFormula a))
                   | SupsetClosed (LinearCtxt (F.BioFormula a))
                   deriving (Eq, Ord, Show)
newtype CtrlSet a = CS
  { unCS :: S.Set (CtrlSetCtxt a)
  } deriving (Eq, Ord, Monoid, Show)
newtype ElemBase a = EB
  { unEB :: LinearCtxt (F.BioFormula a)
  } deriving (Eq, Ord, Monoid, Show)

fromFoldableCtxts :: (Ord a, Foldable f) => f (CtrlSetCtxt a) -> CtrlSet a
fromFoldableCtxts = CS . S.fromList . toList

toCtxtList :: CtrlSet a -> [CtrlSetCtxt a]
toCtxtList = S.toList . unCS

respectsCtrlSet :: (Ord a, Eq a) => ElemBase a -> CtrlSet a -> Bool
respectsCtrlSet f = and . S.map (respectsCtrlCtxt f) . unCS

respectsCtrlCtxt :: (Eq a, Ord a) => ElemBase a -> CtrlSetCtxt a -> Bool
respectsCtrlCtxt (EB base) (Regular ctxt) = not (base == ctxt)
respectsCtrlCtxt (EB base) (SupsetClosed ctxt) = not (ctxt `subCtxtOf` base)

instance Ord a => F.ElemBase ElemBase a where
  formulaBase (F.Atom bf) = EB (singletonCtxt bf)
  formulaBase (F.Conj f1 f2 _) = F.formulaBase f1 <> F.formulaBase f2
  formulaBase (F.Impl' (F.ImplF f1 eb cs f2 _)) = eb

instance Ord a => F.ControlSet CtrlSet a where

instance Ord a => F.BaseCtrl ElemBase CtrlSet a where
  respects = respectsCtrlSet
