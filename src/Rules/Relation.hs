{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors
  -Wno-partial-type-signatures -Wno-incomplete-patterns #-}

{-| Module of derived rule relations. -}

module Rules.Relation
  ( Rule
  , focus
  , implLeft
  , implRight
  , copyRule
  ) where

import Data.Monoid
import Data.Foldable
import Prelude hiding (init, fail)
import Control.Applicative
import Control.Monad.Fail
import Control.Monad hiding (fail)
import Rel
-- import DerivationTerm
-- import ForwardSequent
import LinearContext
-- import Prover (SearchPair(..))

import Data.Constraint
import UnrestrContext

import Rules.Interface

--------------------------------------------------------------------------------

type Rule term fr =
  Relation term (Ax fr) fr (Cty fr) (DTSequent term (Ax fr) fr (Cty fr))

class IsFocusable (k :: FKind) where
instance IsFocusable KAtom where
instance IsFocusable KConj where

type FocMatchRes fr = MatchRes FullXiEmptyResult (Ax fr) fr
type DTFocMatchRes term fr = DT term (FocMatchRes fr)
type DTMatchRes term actcase fr = DT term (MatchRes actcase (Ax fr) fr)

--------------------------------------------------------------------------------

matchLinearCtxt
  :: forall m frml . (MonadFail m, Formula frml)
  => SchemaLCtxt frml -> LCtxt frml -> m (LCtxt frml)
matchLinearCtxt (SLC slc) lc =
  asFoldable (foldrM removeM lc) slc

match
  :: (MonadFail m, Formula frml)
  => SSchema act frml (Cty frml)
  -> DTSequent term (Ax frml) frml (Cty frml)
  -> m (DTMatchRes term act frml)
match (SSEmptyGoal delta) (DT term (NS gamma delta' cty goal)) = do
  delta'' <- matchLinearCtxt delta delta'
  return (DT term (MRFullGoal gamma delta'' cty goal))

positiveFocalDispatch
  :: forall frml term k.
     (Formula frml, Monoid (Cty frml), DerTerm term frml, Ord (Ax frml))
  => frml k -> Relation term (Ax frml) frml (Cty frml) (DTFocMatchRes term frml)
positiveFocalDispatch formula =
  case cases formula of
    AtomCase Dict ->
      case reprAtom formula of
        AR a _ ->
          return $
          DT (init @_ @frml a)
             (MREmptyGoal mempty (singletonCtxt (N formula)))
    ImplCase Dict -> liftFun $ \inputSeq -> match schema inputSeq
      where schema = SSFullGoal mempty mempty (O formula)
    ConjCase Dict ->
      case reprConj formula of
        CR f1 f2 _ -> do
          DT d1 (MREmptyGoal gamma1 delta1) <- positiveFocalDispatch f1
          DT d2 (MREmptyGoal gamma2 delta2) <- positiveFocalDispatch f2
          return $
            DT (conjR d1 d2 formula) (MREmptyGoal (gamma1 <> gamma2) (delta1 <> delta2))

leftActive
  :: Formula frml => LCtxt frml
  -> [Opaque frml]
  -> ZetaXi act frml
  -> Relation term axs frml (Cty frml) (DTMatchRes term act frml)
leftActive delta omega zetaxi =
  case omega of
    [] -> undefined
    (O f):rest ->
      case cases f of
        AtomCase Dict -> leftActive (add (N f) delta) rest zetaxi
        ConjCase Dict -> case reprConj f of
          CR f1 f2 _ -> do
            (DT d res) <- leftActive delta (O f2 : O f1 : rest) zetaxi
            return (DT undefined res)
        ImplCase Dict -> leftActive (add (N f) delta) rest zetaxi

matchRel
  :: Formula frml
  => LCtxt frml
  -> ZetaXi act frml
  -> Relation term (Ax frml) frml (Cty frml) (DTMatchRes term act frml)
matchRel delta zetaxi = liftFun $ \inputSeq -> match schema inputSeq
  where
    schema =
      case zetaxi of
        EmptyZetaXi -> SSEmptyGoal (SLC delta)
        FullZetaXi cty g -> SSFullGoal (SLC delta) cty g

focus
  :: ( IsFocusable k
     , Formula frml
     , Monoid (Cty frml)
     , DerTerm term frml
     , Ord (Ax frml)
     )
  => frml k -> Rule term frml
focus formula = do
  DT d (MREmptyGoal gamma delta) <- positiveFocalDispatch formula
  return $ DT d (NS gamma delta mempty (O formula))

implLeft
  :: (Formula frml, HasBaseCtrl frml, DerTerm term frml, Ord (Ax frml))
  => frml KImpl -> Rule term frml
implLeft fr = case reprImpl fr of
  IR f1 _ cty f2 _ -> do
    DT d (MREmptyGoal gamma1 delta1) <- positiveFocalDispatch f1
    DT d' (MRFullGoal gamma2 delta2 cty' concl) <-
      leftActive mempty [(O f2)] EmptyZetaXi
    guard (respects (lcBase delta2) cty)
    return $
      DT undefined
         (NS (gamma1 <> gamma2)
               (add (N fr) (delta1 <> delta2))
               (cty <> cty')
               concl)

copyRule
  :: (HasBaseCtrl frml, HasAxiom frml, DerTerm term frml, Ord (Ax frml))
  => Ax frml -> Rule term frml
copyRule ax =
  case reprImpl (axIsFormula ax) of
    IR f1 _ cty f2 pay -> do
      DT d (MREmptyGoal gamma1 delta1) <- positiveFocalDispatch f1
      DT d' (MRFullGoal gamma2 delta2 cty' concl) <-
        leftActive mempty [(O f2)] EmptyZetaXi
      guard (respects (lcBase delta2) cty)
      return $
        DT
          undefined
          (NS (add ax (gamma1 <> gamma2)) (delta1 <> delta2) (cty <> cty') concl)

implRight
  :: (Formula frml, HasBaseCtrl frml)
  => frml KImpl -> Rule term frml
implRight fr =
  case reprImpl fr of
    IR f1 eb cty f2 _ -> do
      DT d (MREmptyGoal gamma delta) <-
        leftActive mempty [(O f1)] (FullZetaXi cty (O f2))
      guard ((lcBase delta) == eb)
      return $ DT undefined (NS gamma delta mempty (O fr))

--------------------------------------------------------------------------------

lcBase
  :: forall frml. (HasElemBase frml, Formula frml) => LCtxt frml -> Eb frml
lcBase ctxt = asFoldable (elemBaseAll . fmap nIsOl . toList) ctxt
  where
    nIsOl :: Neutral frml -> Opaque frml
    nIsOl (N f) = O f
