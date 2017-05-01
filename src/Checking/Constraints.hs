{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall #-}

module Checking.Constraints where

import Prelude hiding (fail)
import Checking.World
import LinearContext
import SFormula

data BioConstraintSchema a :: * where
  Respect
    :: LinearCtxt (SFormula a) -> ControlSetSchema a -> BioConstraintSchema a
  And
    :: BioConstraintSchema a
    -> BioConstraintSchema a
    -> BioConstraintSchema a
  Or
    :: BioConstraintSchema a
    -> BioConstraintSchema a
    -> BioConstraintSchema a

checkSchema
  :: Ord a => World a -> BioConstraintSchema a -> Bool
checkSchema w (Respect ctxt css) =
  notIntersecate (ctxtElemBases w ctxt) (fromSchema w css)
checkSchema w (And c1 c2) = (checkSchema w c1) && (checkSchema w c2)
checkSchema w (Or c1 c2) = (checkSchema w c1) || (checkSchema w c2)
