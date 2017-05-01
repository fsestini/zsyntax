{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

module Checking.World
  ( ElementaryBases
  , ControlSet
  , ControlSetSchema(..)
  , World
  , WorldExtSchema(..)
  , wCtrl
  , wElem
  , notIntersecate
  , fromExtension
  , ctxtElemBases
  , fromSchema
  , isEmpty
  , emptyWorld
  , withAxiom
  , extendWorld
  ) where

import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import SFormula
import qualified Data.Map as M
import qualified Data.Set as S
import LinearContext

--------------------------------------------------------------------------------
-- Elementary bases and control sets

type ElementaryContext a = LinearCtxt (BioFormula a)

type ElementaryBase a = ElementaryContext a
newtype ElementaryBases a =
  EB (S.Set (ElementaryBase a))
  deriving (Eq, Monoid)
newtype ControlSet a =
  CS (S.Set (ElementaryContext a))
  deriving (Eq)

instance Ord a =>
         Monoid (ControlSet a) where
  mempty = CS mempty
  (CS cs1) `mappend` (CS cs2) = CS $ foldr addCS cs2 cs1
    where
      addCS newCtxt = S.insert newCtxt . S.filter (not . (newCtxt `subCtxtOf`))

notIntersecate
  :: Ord a
  => ElementaryBases a -> ControlSet a -> Bool
notIntersecate (EB bases) (CS ctrlset) =
  and $ [not (violates base ctxt) | base <- listBases, ctxt <- listCtrl]
  where
    listBases = S.toList bases
    listCtrl = S.toList ctrlset
    violates = flip subCtxtOf

--------------------------------------------------------------------------------

type WorldMap a s = M.Map (SFormula a, SFormula a) s

type CtrlMap a = WorldMap a (ControlSet a)
type ElemMap a = WorldMap a (ElementaryBases a)

data World a = W
  { ctrlMap :: CtrlMap a
  , elemMap :: ElemMap a
  }
  deriving (Eq)

emptyWorld :: World a
emptyWorld = W M.empty M.empty

wCtrl :: Ord a => World a -> SFormula a -> SFormula a -> ControlSet a
wCtrl w f1 f2 = fromMaybe mempty $ M.lookup (f1, f2) (ctrlMap w)

wElem :: Ord a => World a -> SFormula a -> SFormula a -> ElementaryBases a
wElem w f1 f2 = fromMaybe mempty $ M.lookup (f1, f2) (elemMap w)

data WorldExtSchema a =
  WES (LinearCtxt (SFormula a))
      (SFormula a)
      (ControlSetSchema a)
      (SFormula a)

newtype ControlSetSchema a =
  CSS { unCSS :: S.Set (SFormula a, SFormula a) }
  deriving (Monoid)

fromSchema :: Ord a => World a -> ControlSetSchema a -> ControlSet a
fromSchema w = mconcat . map (uncurry (wCtrl w)) . S.toList . unCSS

withAxiom
  :: (Ord a, Foldable f)
  => SFormula a -> SFormula a -> f (ElementaryContext a) -> World a -> World a
withAxiom a b ctrl = extendWorld [mempty] a ctrl b

extendWorld
  :: (Ord a, Foldable f, Foldable g)
  => f (ElementaryContext a)
  -> SFormula a
  -> g (ElementaryContext a)
  -> SFormula a
  -> World a
  -> World a
extendWorld bases a ctrl b =
  transformCtrl (extendMap a b (CS (S.fromList (toList ctrl)))) .
  transformElem (extendMap a b (EB (S.fromList (toList bases))))

isEmpty :: ControlSetSchema a -> Bool
isEmpty (CSS set) = S.null set

fromExtension
  :: Ord a
  => WorldExtSchema a -> World a -> World a
fromExtension (WES ctxt a css b) w =
  transformCtrl (extendMap a b (fromSchema w css)) $
  transformElem (extendMap a b (ctxtElemBases w ctxt)) w

transformCtrl :: (CtrlMap a -> CtrlMap a) -> World a -> World a
transformCtrl trans (W ctrlM elemM) = W (trans ctrlM) elemM

transformElem :: (ElemMap a -> ElemMap a) -> World a -> World a
transformElem trans (W ctrlM elemM) = W ctrlM (trans elemM)

mix :: Ord a => ElementaryBases a -> ElementaryBases a -> ElementaryBases a
mix (EB bases1) (EB bases2) = EB . S.fromList $ do
  base1 <- S.toList bases1
  base2 <- S.toList bases2
  return $ base1 `mappend` base2

ctxtElemBases
  :: Ord a
  => World a -> LinearCtxt (SFormula a) -> ElementaryBases a
ctxtElemBases w ctxt = foldr1 mix $ map elemBases . toList $ ctxt
  where
    elemBases (SAtom atom) = EB . S.singleton . singletonCtxt $ atom
    elemBases (SConj f1 f2) = mix (elemBases f1) (elemBases f2)
    elemBases (SImpl f1 f2) = wElem w f1 f2

extendMap
  :: (Monoid s, Ord a)
  => SFormula a -> SFormula a -> s -> WorldMap a s -> WorldMap a s
extendMap f1 f2 set = M.insertWith mappend (f1,f2) set
