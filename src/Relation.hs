{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors
  -Wno-partial-type-signatures -Wno-incomplete-patterns #-}

{-| Module of derived rule relations. -}

module Relation
  ( positiveFocalDispatch
  , focus
  , implLeft
  , copyRule
  , implRight
  , Rule
  , DT(..)
  , DTSequent
  ) where

import Data.Monoid
import Data.Foldable
import Prelude hiding (init, fail)
import Control.Applicative
import Control.Monad.Fail
import RelFormula
import Control.Monad hiding (fail)
import Rel
import DerivationTerm
import ForwardSequent
import LinearContext
import Prover (SearchPair(..))
import qualified Data.Map as M

--------------------------------------------------------------------------------

-- | Type of labelled sequents decorated with derivation terms
data DT term a l = DT term (M.Map l Int) a
  deriving (Eq, Ord)

instance (Show term, Show a) =>
         Show (DT term a l) where
  show (DT t m x) = show . sum . M.elems $ m
    -- show t ++ ("(" ++ (show . sum . M.elems $ m) ++ ")") ++ " :: " ++ show x

type DTSequent term eb cs a l = DT term (NeutralSequent eb cs a l) l

instance (Ord l, Ord a, Eq (cs a)) =>
         ForwardSequent (DTSequent term eb cs a l) where
  subsumes (DT _ _ s1) (DT _ _ s2) = subsumes s1 s2

instance (SearchPair seqty goalty, ForwardSequent (DT term seqty l)) =>
         SearchPair (DT term seqty l) goalty where
  isSubsequent (DT _ _ s1) s2 = isSubsequent s1 s2
  subsumesGoal (DT _ _ s) g = s `subsumesGoal` g

--------------------------------------------------------------------------------

class IsFocusable (k :: FKind) where
instance IsFocusable KAtom where
instance IsFocusable KConj where

--------------------------------------------------------------------------------

{-| Type of relations.

    A relation is an unbounded curried function of labelled sequents.  It is
    parameterized by the type of labels and biological atoms of the input
    labelled sequents, and by the codomain type of the relation. -}
type Relation term eb cs a l b = Rel (DTSequent term eb cs a l) b

--------------------------------------------------------------------------------
-- Sequent schemas.

-- | Type of linear contexts which appear in sequent schemas.
newtype SchemaLCtxt eb cs a l = SLC (LCtxt eb cs a l) deriving (Monoid)

matchLinearCtxt
  :: forall m a l eb cs . (MonadFail m, Ord a, Ord l)
  => SchemaLCtxt eb cs a l -> LCtxt eb cs a l -> m (LCtxt eb cs a l)
matchLinearCtxt (SLC slc) lc = asFoldable (foldrM r lc) slc
  where
    r :: NeutralFormula eb cs a l -> _ -> m (_)
    r = removeM

--------------------------------------------------------------------------------
-- Act relations.

{-| Type indicating the possible shapes of an active relation.

    An active relations has the form

      act(delta ; omega ==>_zeta xi)[...] -> gamma' ; delta' -->> res

    where either
    1. xi is a formula, zeta is a control set, and res is empty, or
    2. xi is empty, zeta is empty, and res is a formula.
    -}
data ActCase = FullXiEmptyResult | EmptyXiFullResult

data SequentSchema :: (* -> *) -> (* -> *) -> ActCase -> * -> * -> * where
  SSEmptyGoal :: (SchemaLCtxt eb cs a l) -> SequentSchema eb cs EmptyXiFullResult a l
  SSFullGoal
    :: (SchemaLCtxt eb cs a l)
    -> cs a
    -> OLFormula eb cs a l
    -> SequentSchema eb cs FullXiEmptyResult a l

data MatchResult :: (* -> *) -> (* -> *) -> ActCase -> * -> * -> * where
  MREmptyGoal
    :: UCtxt eb cs a l
    -> LCtxt eb cs a l
    -> MatchResult eb cs FullXiEmptyResult a l
  MRFullGoal
    :: UCtxt eb cs a l
    -> LCtxt eb cs a l
    -> cs a
    -> OLFormula eb cs a l
    -> MatchResult eb cs EmptyXiFullResult a l

type DTMatchResult term eb cs actcase a l = DT term (MatchResult eb cs actcase a l) l

{-| Matches a labelled sequent against an act sequent schema.
    Returns the result in a MonadFail instance, which signals the error in case
    the match fails. -}
match
  :: (Eq a, Eq l, Eq (cs a), MonadFail m, Alternative m, Ord a, Ord l)
  => SequentSchema eb cs ac a l
  -> DTSequent term eb cs a l
  -> m (DTMatchResult term eb cs ac a l)
match (SSEmptyGoal delta) (DT term m (NS gamma delta' cs goal)) = do
  delta'' <- matchLinearCtxt delta delta'
  return $ DT term m (MRFullGoal gamma delta'' cs goal)
match (SSFullGoal delta cs goal) (DT term m (NS gamma delta' cs' goal')) =
  guard (goal == goal') >> guard (cs == cs') >>
  DT term m <$> (MREmptyGoal gamma <$> matchLinearCtxt delta delta')

type FocMatchRes eb cs a l = MatchResult eb cs FullXiEmptyResult a l
type DTFocMatchResult term eb cs a l = DT term (FocMatchRes eb cs a l) l

{-| Positive focal relation.
    The fact that it returns a result sequent with empty goal is statically
    enforced by the type of the function. -}
positiveFocalDispatch
  :: forall term eb cs a l k . ( Monoid (cs a)
     , Eq a
     , Eq (cs a)
     , Eq l
     , Ord l
     , Ord a
     , DerTerm term eb cs a l
     )
  => LFormula eb cs k a l
  -> Relation term eb cs a l (DTFocMatchResult term eb cs a l)
positiveFocalDispatch formula =
  case formula of
    Atom a ->
      return
        (DT (init @_ @eb @cs @_ @l a) mempty
           (MREmptyGoal mempty (singletonCtxt (NF formula))))
    Impl _ _ _ _ _ -> liftFun $ \inputSeq -> match schema inputSeq
      where schema = SSFullGoal mempty mempty (OLF formula)
    Conj f1 f2 _ -> do
      DT d1 m1 (MREmptyGoal gamma1 delta1) <- positiveFocalDispatch f1
      DT d2 m2 (MREmptyGoal gamma2 delta2) <- positiveFocalDispatch f2
      return $
        DT (conjR d1 d2 formula) (M.unionWith (+) m1 m2)
           (MREmptyGoal (gamma1 <> gamma2) (delta1 <> delta2))

data ZetaXi :: (* -> *) -> (* -> *) -> ActCase -> * -> * -> * where
  FullZetaXi
    :: (cs a) -> (OLFormula eb cs a l) -> ZetaXi eb cs FullXiEmptyResult a l
  EmptyZetaXi :: ZetaXi eb cs EmptyXiFullResult a l

{-| Left active relation, that is active relation of the form

      act(delta ; omega ===> Q)

    where xi is Q, hence a right-synchronous formula (and of course
    non-empty).

    Notice how the typeclass context enforces that the input formula is indeed
    right-synchronous. -}
leftActive
  :: (DerTerm term eb cs a l, Ord a, Ord l, Eq (cs a))
  => (LCtxt eb cs a l)
  -> [OLFormula eb cs a l]
  -> ZetaXi eb cs actcase a l
  -> Relation term eb cs a l (DTMatchResult term eb cs actcase a l)
leftActive delta omega zetaxi =
  case omega of
    [] -> matchRel delta zetaxi
    (OLF f@(Conj f1 f2 _):rest) -> do
      (DT d m res) <- leftActive delta (OLF f2 : OLF f1 : rest) zetaxi
      return (DT (conjL d f) m res)
    (OLF fr@(Impl _ _ _ _ _):rest) -> leftActive (add (NF fr) delta) rest zetaxi
    (OLF fr@(Atom _):rest) -> leftActive (add (NF fr) delta) rest zetaxi

{-| Active match relation.
    It requires the input xi formula (if any) to be right-synchronous (otherwise
    we would have a right active relation). -}
matchRel
  :: (Eq a, Eq l, Eq (cs a), Ord l, Ord a)
  => (LCtxt eb cs a l)
  -> ZetaXi eb cs actcase a l
  -> Relation term eb cs a l (DTMatchResult term eb cs actcase a l)
matchRel delta zetaxi =
  liftFun $ \inputSeq -> match schema inputSeq
  where
    schema =
      case zetaxi of
        EmptyZetaXi -> SSEmptyGoal (SLC delta)
        FullZetaXi cs g -> SSFullGoal (SLC delta) cs g

--------------------------------------------------------------------------------
-- Forward derived rules

type Rule term eb cs a l = Relation term eb cs a l (DTSequent term eb cs a l)

focus
  :: (IsFocusable k, ControlSet cs a, Ord l, Ord a, DerTerm term eb cs a l)
  => LFormula eb cs k a l
  -> Rule term eb cs a l
focus formula = do
  DT d m (MREmptyGoal gamma delta) <- positiveFocalDispatch formula
  return $ DT d m (NS gamma delta mempty (OLF formula))

implLeft
  :: (BaseCtrl eb cs a, Ord l, Ord a, DerTerm term eb cs a l)
  => ImplFormula eb cs IRegular a l
  -> Rule term eb cs a l
implLeft fr@(ImplF a _ cs b _) = do
  DT d m1 (MREmptyGoal gamma1 delta1) <- positiveFocalDispatch a
  DT d' m2 (MRFullGoal gamma2 delta2 cs' concl) <-
    leftActive mempty [(OLF b)] EmptyZetaXi
  guard (respects (elemBaseAll delta2) cs)
  return $
    DT (implL d d' fr) (M.unionWith (+) m1 m2)
       (NS (gamma1 <> gamma2)
           (add (NF (Impl' fr)) (delta1 <> delta2))
           (cs <> cs')
           concl)

copyRule
  :: (BaseCtrl eb cs a, Ord l, Ord a, DerTerm term eb cs a l)
  => Axiom eb cs a l
  -> Rule term eb cs a l
copyRule fr@(ImplF a EmptySpot cs b l) = do
  DT d m1 (MREmptyGoal gamma1 delta1) <- positiveFocalDispatch a
  DT d' m2 (MRFullGoal gamma2 delta2 cs' concl) <-
    leftActive mempty [(OLF b)] EmptyZetaXi
  let m = M.unionWith (+) m1 m2
  guard (respects (elemBaseAll delta2) cs)
  guard (not . atThreshold . M.lookup l $ m)
  --guard (not . (> 20) . sum . M.elems $ m)
  return $
    DT (copy (implL d d' (axiomIsRegular fr)) fr)
       (M.alter updater l $ m)
       (NS (add fr (gamma1 <> gamma2)) (delta1 <> delta2) (cs <> cs') concl)
  where
    updater Nothing = Just 1
    updater (Just n) = Just (n + 1)
    atThreshold Nothing = False
    atThreshold (Just x) = x > 13

implRight
  :: (BaseCtrl eb cs a, Ord l, Ord a, DerTerm term eb cs a l)
  => ImplFormula eb cs IRegular a l
  -> Rule term eb cs a l
implRight fr@(ImplF a (FullSpot eb) cs b _) = do
  DT d m (MREmptyGoal gamma delta) <-
    leftActive mempty [(OLF a)] (FullZetaXi cs (OLF b))
  guard ((elemBaseAll delta) == eb)
  return $ DT (implR d fr) m (NS gamma delta mempty (OLF (Impl' fr)))
