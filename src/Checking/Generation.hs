{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}

module Checking.Generation where

import Data.Foldable (toList, foldrM)
import Data.List (nub)
import Data.Maybe
import LabelledSequent
import Checking.Constraints
import Data.Monoid hiding (Sum)
import Control.Monad.Except
import Checking.DerivationTerm
import qualified Data.Set as S
import Formula
import Control.Monad.Fail
import Control.Monad hiding (fail)

class ConstraintMonad m l a where
  unifyB :: BioEqConstraint l a -> m l a ()
  unifyC :: CtrlEqConstraint l a -> m l a ()
  addBioConstraint :: BioConstraint l a -> m l a ()
  getBioConstraints :: m l a [BioConstraint l a]

addLabel
  :: (ConstraintMonad m l a, Monad (m l a), Ord a, Ord l)
  => l -> BCSchema l a -> LinearCtxt l a -> m l a (LinearCtxt l a)
addLabel lbl bs ctxt = do
  unifyB (VarConstr lbl bs)
  return (add (L lbl) ctxt)

generateConstraints
  :: (Ord a, Ord l, MonadFail (m l a), ConstraintMonad m l a)
  => DerTerm l a -> m l a [BioConstraint l a]
generateConstraints term = generateConstraints' term >> getBioConstraints

-- Returns the control set schema of the sequent, the linear context
-- represented as a set of labels, and the label of the conclusion.
-- NOTE!!: we are (and should be) operating under the assumption that formulas
-- in the unrestricted context have null biocore (only implicational formulas
-- with null biocore).
generateConstraints'
  :: (Ord a, Ord l, MonadFail (m l a), ConstraintMonad m l a)
  => DerTerm l a -> m l a (CSSchema l a, LinearCtxt l a, Label l a)
generateConstraints' (Init atom) =
  return (Set mempty, singletonLinearCtxt (A atom), A atom)
generateConstraints' (Copy d l) = do
  (css, ctxt, concl) <- generateConstraints' d
  ctxt' <- remove l ctxt
  return (css, ctxt', concl)
generateConstraints' (ConjR d1 d2 r) = do
  (css1, ctxt1, concl1) <- generateConstraints' d1
  (css2, ctxt2, concl2) <- generateConstraints' d2
  let bc1 = biocore ctxt1
      bc2 = biocore ctxt2
      core2 = biocoreOutofLabel concl2
      core1 = biocoreOutofLabel concl1
  addBioConstraint $
    ((Respect bc1 css2) `And` Respect core2 css1) `Or`
    ((Respect bc2 css1) `And` Respect core1 css2)
  return (css1 `Sum` css2, ctxt1 <> ctxt2, L r)
generateConstraints' (ConjL d l1 l2 l) = do
  (css, ctxt, concl) <- generateConstraints' d
  let bs = biocoreOutofLabel l1 `Sum` biocoreOutofLabel l2
  ctxt' <- remove l1 >=> remove l2 >=> addLabel l bs $ ctxt
  return (css, ctxt', concl)
generateConstraints' (ImplR d l r bs cs) = do
  (css, ctxt, _) <- generateConstraints' d
  ctxt' <- remove l ctxt
  let bc = biocore ctxt'
  case bs of
    Just set -> unifyB (SetConstr set bc)
    Nothing -> unifyB (VarConstr r bc)
  case cs of
    Just set -> unifyC (SetConstr set css)
    Nothing -> unifyC (VarConstr r css)
  return (Set mempty, ctxt', L r)
generateConstraints' (ImplL d1 d2 l s bs cs) = do
  (css1, ctxt1, _) <- generateConstraints' d1
  (css2, ctxt2full, concl2) <- generateConstraints' d2
  ctxt2 <- remove l ctxt2full
  let bc = biocore ctxt2
      formulaCS = fromMaybe (Label s) (fmap Set cs)
      formulaBS = fromMaybe (Label s) (fmap Set bs)
  addBioConstraint (Respect bc formulaCS)
  unifyC (SetConstr mempty css1)
  ctxt <- addLabel s formulaBS (ctxt1 <> ctxt2)
  return (css2 `Sum` formulaCS, ctxt, concl2)

biocoreOutofLabel :: Label l a -> BCSchema l a
biocoreOutofLabel (L l) = Label l
biocoreOutofLabel (A a) = Set (bsSingleton a)

biocore :: (Ord a, Ord l) => LinearCtxt l a -> BCSchema l a
biocore =
  asFoldable (foldr Sum (Set mempty) . fmap doTheDwaine . nub . toList)
  where
    doTheDwaine (L l) = Label l
    doTheDwaine (A a) = Set (bsSingleton a)

-- returnUpdated
--   :: (CSSchema l a, LinearCtxt l a, Label l a)
--   -> Unif (CSSchema l a, LinearCtxt l a, Label l a)
-- returnUpdated (css, ctxt, lbl) = do
--   newCss <- applyCurrentSubCS css
--   return (newCss, ctxt, lbl)

-- class (CanUnify m, MonadFail m) => HasSetInfo m where
--   addBiocoreSchema :: Label l a -> BCSchema l a -> m ()
--   getBiocoreSchema :: Label l a -> m (BCSchema l a)
--   addControlSchema :: Label l a -> CSSchema l a -> m ()
--   getControlSchema :: Label l a -> m (CSSchema l a)

-- instance HasSetInfo Unif where

-- addCore :: Label l a ->

-- labelControl :: Label l a -> CSSchema l a
-- labelControl = undefined

-- labelCore :: Label l a -> BCSchema l a
-- labelCore (L l) = Label l
-- labelCore (A a) = Set (bsSingleton a)
