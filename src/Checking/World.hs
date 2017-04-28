{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Checking.World where

{-|

A world is a pair of maps (w_ctrl, w_elem) of type

  Formulas x Formulas -> (power(BioFormula), power(BioFormula))

Actually, we represent power(BioFormula) with a subset of BioFormula.

-}

import Formula -- From here we import ControlSet as ElementaryBase.
import qualified Data.Map as M

--------------------------------------------------------------------------------
-- Simple formulas

-- | Type of simple formulas.
data SFormula a where
  SAtom :: BioFormula a -> SFormula a
  SConj :: SFormula a -> SFormula a -> SFormula a
  SImpl :: SFormula a -> SFormula a -> SFormula a
  deriving (Eq, Ord)

fromLFormula :: LFormula p l a -> SFormula a
fromLFormula = undefined

--------------------------------------------------------------------------------

type WorldMap a s = M.Map (SFormula a, SFormula a) s

type CtrlMap a = WorldMap a (ControlSet a)
type ElemMap a = WorldMap a (ElementaryBase a)

data World a = W
  { ctrlMap :: CtrlMap a
  , elemMap :: ElemMap a
  }

extendMap
  :: (Monoid s)
  => SFormula a -> SFormula a -> s -> WorldMap a s -> WorldMap a s
extendMap set map = undefined

-- Gamma*, A |-_G B
extendWorldWith
  :: (Ord a)
  => ElementaryBase a
  -> SFormula a
  -> ControlSet a
  -> SFormula a
  -> World a
  -> World a
extendWorldWith base a ctrl b (W ctrlMap elemMap) =
  W (extendMap a b ctrl ctrlMap) (extendMap a b base elemMap)

class HasWorld m a where
  extendWorld :: ElementaryBase a
              -> SFormula a
              -> ControlSet a
              -> SFormula a
              -> m ()
