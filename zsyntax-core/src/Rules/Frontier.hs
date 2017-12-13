{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Rules.Frontier
  ( GoalNSequent(..)
  , ResultNSequent(..)
  , GNS
  , UnaryRule
  , initialSequentsAndRules
  ) where

import ForwardSequent
import Data.Constraint hiding ((***))
import Prover
import Data.Foldable
import TypeClasses (filterOut, partitionEithers, Pretty, PrettyK)
-- import LabelledSequent
-- import RelFormula
import qualified Data.Set as S
-- import Relation
import Rel (unRel)
import Control.Arrow ((***), (>>>))
import Control.Monad (guard, MonadPlus(..))
-- import DerivationTerm
-- import SFormula (fromLFormula)
import LinearContext

import Rules.Relation
import Rules.Interface

data OpaqueImpl fr = OI (fr KImpl)

instance Formula fr => Eq (OpaqueImpl fr) where
  (OI f1) == (OI f2) = (O f1) == (O f2)
instance Formula fr => Ord (OpaqueImpl fr) where
  compare (OI f1) (OI f2) = compare (O f2) (O f2)

data DecFormula :: * -> (FKind -> *) -> * where
  Unrestr :: ax -> DecFormula ax frml
  LinNeg :: OpaqueImpl frml -> DecFormula ax frml
  LinPos :: Opaque frml -> DecFormula ax frml

deriving instance (Eq ax, Formula frml) => Eq (DecFormula ax frml)
deriving instance (Ord ax, Formula frml) => Ord (DecFormula ax frml)

--------------------------------------------------------------------------------
-- Goal and result sequents.

-- | Linear contexts in goal neutral sequents.
type GLCtxt fr = NonEmptyLinearCtxt (Neutral fr)

data GoalNSequent ax fr =
  GNS (UCtxt ax) (GLCtxt fr) (Opaque fr)
  deriving (Eq, Ord)

data ResultNSequent ax fr cty = RNS
  { rnsUc :: UCtxt ax
  , rnsLc :: GLCtxt fr
  , rnsCty :: cty
  , rnsConcl :: Opaque fr
  }

toGNSequent
  :: Formula fr
  => NSequent ax fr cty -> Maybe (GoalNSequent ax fr)
toGNSequent (NS uc lc cty f) = do
  nelc <- fromLC lc
  return (GNS uc nelc f)

toRNSequent :: cty -> GoalNSequent ax fr -> ResultNSequent ax fr cty
toRNSequent cty (GNS uc lc c) = RNS uc lc cty c

toNSequent :: Formula fr => GoalNSequent ax fr -> NSequent ax fr ()
toNSequent (GNS uc lc c) = NS uc (toLC lc) () c

instance (Formula fr, Ord ax, Pretty ax, PrettyK fr) =>
         ForwardSequent (GoalNSequent ax fr) where
  subsumes gns1 gns2 = toNSequent gns1 `subsumes` toNSequent gns2

instance (Formula frml, Ord axs, Pretty axs, PrettyK frml, Eq cty) =>
         SearchTriple (NSequent axs frml cty)
                      (GoalNSequent axs frml)
                      (ResultNSequent axs frml cty) where
  subsumesGoal ns@ (NS _ _ cty _) gns = do
    case toGNSequent ns of
      Nothing -> return mzero
      Just goaled -> do
        b <- goaled `subsumes` gns
        return $ guard b >> return (toRNSequent cty goaled)

type GNS fr = GoalNSequent (Ax fr) fr
type DecF fr = DecFormula (Ax fr) fr

--------------------------------------------------------------------------------
-- Frontier computation

filterImpl :: [Neutral fr] -> [OpaqueImpl fr]
filterImpl = filterOut . map aux
  where
    aux :: Neutral fr -> Maybe (OpaqueImpl fr)
    aux (N (f :: frml k)) =
      either (const Nothing) (\Dict -> Just (OI f)) (decideNeutral @k)

-- | Computes the frontier of a sequent.
frontier
  :: (Formula fr, Ord (Ax fr), HasAxiom fr) => GNS fr -> S.Set (DecF fr)
frontier (GNS uc lc (O goal)) =
  toplevelUC <> toplevelLC <> S.singleton (LinPos (O goal)) <>
  ucFrontier <>
  linFrontier <>
  goalFrontier
  where
    toplevelUC = (S.fromList . map Unrestr . asFoldable toList $ uc)
    toplevelLC =
      (S.fromList . map LinNeg . filterImpl . asFoldable toList $ lc)
    ucFrontier =
      fold . map (frNeg . N . axIsFormula) . asFoldable toList $ uc
    linFrontier = fold . map frNeg . asFoldable toList $ lc
    goalFrontier = frPos goal

frNeg :: (Formula fr, Ord ax) => Neutral fr -> S.Set (DecFormula ax fr)
frNeg (switchN -> Left (AR _ _)) = mempty
frNeg (switchN -> Right (IR a _ _ b _)) = foc a <> act b

frPos :: (Formula fr, Ord ax) => fr k -> S.Set (DecFormula ax fr)
frPos f =
  case switchF' f of
    T1 (AR _ _) -> mempty
    T2 (CR _ _ _) -> foc f
    T3 (IR a _ _ b _) -> act a <> frPos b <> S.singleton (LinPos (O b))

foc :: (Formula fr, Ord ax) => fr k -> S.Set (DecFormula ax fr)
foc f = case switchF' f of
  T1 (AR _ _) -> mempty
  T2 (CR f1 f2 _) -> foc f1 <> foc f2
  T3 (IR a _ _ b _) -> S.singleton (LinPos (O f)) <> frPos f

act :: (Formula fr, Ord ax) => fr k -> S.Set (DecFormula ax fr)
act f =
  case switchF f of
    T1 (_, AR _ _) -> mempty
    T2 (_, CR f1 f2 _) -> act f1 <> act f2
    T3 (Dict, IR a _ _ b _) -> S.singleton (LinNeg (OI f)) <> frPos f

--------------------------------------------------------------------------------
-- Generation of initial rules from the frontier.

generateRule
  :: (Formula fr, Ord (Ax fr), HasBaseCtrl fr, HasAxiom fr, DerTerm term fr)
  => DecF fr -> Rule term fr
generateRule f =
  case f of
    Unrestr axiom -> copyRule axiom
    LinNeg (OI impl) -> implLeft impl
    LinPos (O orf) ->
      case (switchF orf) of
        T1 (Dict, AR _ _) -> focus orf
        T2 (Dict, CR _ _ _) -> focus orf
        T3 (Dict, IR a eb cs b _) -> implRight orf

--------------------------------------------------------------------------------
-- Main function

type UnaryRule term fr = DTS term fr -> Rule term fr
type DTS term fr =
  DT term (NSequent (Ax fr) fr (Cty fr))

initialSequentsAndRules
  :: (HasBaseCtrl fr, DerTerm term fr, Ord term, HasAxiom fr, Ord (Ax fr))
  => GNS fr -> (S.Set (DTS term fr), [UnaryRule term fr])
initialSequentsAndRules =
  frontier >>>
  S.toList >>>
  map generateRule >>>
  map unRel >>>
  filterOut >>>
  partitionEithers >>>
  (S.fromList *** id)
