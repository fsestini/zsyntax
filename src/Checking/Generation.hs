{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

{-| World updating and generation of biological constraints from a derivation
  term. -}

module Checking.Generation (generateConstraints, ConstraintMonad(..)) where

import Prelude hiding (fail)
import LinearContext

import Data.Monoid hiding (Sum)
import DerivationTerm
import qualified Data.Set as S
import Control.Monad.Fail
import SFormula

import Checking.Constraints
import Checking.World

class ConstraintMonad m a where
  addBioConstraint :: BioConstraintSchema a -> m ()
  getBioConstraints :: m [BioConstraintSchema a]
  addExtSchema :: WorldExtSchema a -> m ()
  getExtSchemas :: m [WorldExtSchema a]

{-| Traverses a derivation term and computes the associated biological
    constraints.

    NOTE!!: we are (and should be) operating under the assumption that formulas
    in the unrestricted context are only axioms, that is, have null elementary
    base (only implicational formulas with null elementary base).
-}
generateConstraints
  :: (Ord a, MonadFail m, ConstraintMonad m a)
  => DerTerm l a -> m ([WorldExtSchema a], [BioConstraintSchema a])
generateConstraints term = do
  _ <- generateConstraints' term
  ext <- getExtSchemas
  constr <- getBioConstraints
  return (ext, constr)

generateConstraints'
  :: (Ord a, MonadFail m, ConstraintMonad m a)
  => DerTerm l a -> m (LinearCtxt (SFormula a), ControlSetSchema a, SFormula a)
generateConstraints' (Init atom) =
  return (singletonCtxt (SAtom atom), mempty, (SAtom atom))
generateConstraints' (Copy d _ f) = do
  (ctxt, ctrl, c) <- generateConstraints' d
  return (remove f ctxt, ctrl, c)
generateConstraints' (ConjR d1 d2 _) = do
  (ctxt1, css1, concl1) <- generateConstraints' d1
  (ctxt2, css2, concl2) <- generateConstraints' d2
  let core2 = singletonCtxt concl2
      core1 = singletonCtxt concl1
  addBioConstraint $
    ((Respect ctxt1 css2) `And` Respect core2 css1) `Or`
    ((Respect ctxt2 css1) `And` Respect core1 css2)
  return (ctxt1 <> ctxt2, css1 <> css2, concl1 `SConj` concl2)
generateConstraints' (ConjL d _ f1 _ f2 _) = do
  (ctxt, css, concl) <- generateConstraints' d
  let ctxt' = remove f1 . remove f2 . add (f1 `SConj` f2) $ ctxt
  return (ctxt', css, concl)
generateConstraints' (ImplR d _ a _) = do
  (ctxt, css, b) <- generateConstraints' d
  let ctxt' = remove a ctxt
  addExtSchema (WES ctxt' a css b)
  return (ctxt', mempty, a `SImpl` b)
generateConstraints' (ImplL d1 d2 _ b _) = do
  (ctxt1, css1, a) <- generateConstraints' d1
  (ctxt2full, css2, c) <- generateConstraints' d2
  let ctxt2 = remove b ctxt2full
  if isEmpty css1
    then do
      let ctxt = add (a `SImpl` b) (ctxt1 <> ctxt2)
          abCss = (CSS (S.singleton (a, b)))
      addBioConstraint (Respect ctxt2 abCss)
      return (ctxt, css2 <> abCss, c)
    else fail "ImplL must have empty control set in left premise"
