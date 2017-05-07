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

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

{-| Module of derived rule relations. -}

module Relation
  ( positiveFocalDispatch
  , focal
  , implLeft
  , copyRule
  , implRight
  ) where

-- import SFormula (fromLFormula)
import Data.Monoid
import Control.Applicative
import Prelude hiding (fail)
import Control.Monad.Fail
-- import Formula
import RelFormula
--import LabelledSequent
import Control.Monad hiding (fail)
import Rel
-- import Data.Foldable
-- import DerivationTerm
{-import ForwardSequent-}
import LinearContext
{-import TypeClasses-}

--------------------------------------------------------------------------------

-- -- | Type of labelled sequents decorated with derivation terms
-- data DLSequent l a = DLS
--   { derivation :: DerTerm l a
--   , sequent :: LabelledSequent l a
--   }

-- instance  (Eq a, Eq l) => Eq (DLSequent l a) where
--   (DLS _ s1) == (DLS _ s2) = s1 == s2

-- instance (Ord a, Ord l) => Ord (DLSequent l a) where
--   compare (DLS _ s1) (DLS _ s2) = compare s1 s2

-- instance (Ord l, Ord a) => ForwardSequent (DLSequent l a) where
--   subsumes (DLS d1 s1) (DLS d2 s2) = d1 == d2 && ForwardSequent.subsumes s1 s2

-- instance Coercible (DLSequent l a) (LabelledSequent l a) where
--   coerce (DLS _ s) = s

--------------------------------------------------------------------------------

class IsFocusable (k :: FKind) where
instance IsFocusable KAtom where
instance IsFocusable KConj where

--------------------------------------------------------------------------------

{-| Type of relations.

    A relation is an unbounded curried function of labelled sequents.  It is
    parameterized by the type of labels and biological atoms of the input
    labelled sequents, and by the codomain type of the relation. -}
-- type Relation l a b = Rel (DLSequent l a) b
type Relation eb cs l a b = Rel (NeutralLabelledSequent eb cs l a) b

--------------------------------------------------------------------------------
-- Sequent schemas.

-- | Type of linear contexts which appear in sequent schemas.
newtype SchemaLCtxt eb cs l a = SLC (LCtxt eb cs l a)

matchLinearCtxt
  :: (MonadFail m, Ord a, Ord l)
  => SchemaLCtxt eb cs l a -> LCtxt eb cs l a -> m (LCtxt eb cs l a)
matchLinearCtxt (SLC slc) lc = undefined -- asFoldable (foldrM (removeM) lc) slc
  --matchCtxt slc lc

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
  SSEmptyGoal :: (LCtxt eb cs l a) -> SequentSchema eb cs EmptyXiFullResult l a
  SSFullGoal
    :: (LCtxt eb cs l a)
    -> cs a
    -> ORelFormula eb cs l a
    -> SequentSchema eb cs FullXiEmptyResult l a

data MatchResult :: (* -> *) -> (* -> *) -> ActCase -> * -> * -> * where
  MREmptyGoal
    :: UCtxt eb cs l a
    -> LCtxt eb cs l a
    -> MatchResult eb cs FullXiEmptyResult l a
  MRFullGoal
    :: UCtxt eb cs l a
    -> LCtxt eb cs l a
    -> cs a
    -> ORelFormula eb cs l a
    -> MatchResult eb cs EmptyXiFullResult l a

{-| Matches a labelled sequent against an act sequent schema.
    Returns the result in a MonadFail instance, which signals the error in case
    the match fails. -}
match
  :: (Eq a, Eq l, Eq (cs a), MonadFail m, Alternative m, Ord a, Ord l)
  => SequentSchema eb cs ac l a
  -> NeutralLabelledSequent eb cs l a
  -> m (MatchResult eb cs ac l a)
match (SSEmptyGoal delta) (NLS gamma delta' cs goal) = do
  delta'' <- matchLinearCtxt (SLC delta) delta'
  return $ MRFullGoal gamma delta'' cs goal
match (SSFullGoal delta cs goal) (NLS gamma delta' cs' goal') =
  guard (goal == goal') >> guard (cs == cs') >>
  MREmptyGoal gamma <$> matchLinearCtxt (SLC delta) delta'

type FocMatchRes eb cs l a = MatchResult eb cs FullXiEmptyResult l a

{-| Positive focal relation.
    The fact that it returns a result sequent with empty goal is statically
    enforced by the type of the function. -}
positiveFocalDispatch
  :: (Monoid (cs a), Eq a, Eq (cs a), Eq l, Ord l, Ord a)
  => RelFormula eb cs k l a -> Relation eb cs l a (FocMatchRes eb cs l a)
positiveFocalDispatch formula =
  case formula of
    Atom _ -> return (MREmptyGoal mempty (singletonCtxt (NF formula)))
    Impl _ _ _ _ _ -> liftFun $ \inputSeq -> match schema inputSeq
      where schema = SSFullGoal mempty mempty (ORF formula)
    Conj f1 f2 r -> do
      MREmptyGoal gamma1 delta1 <- positiveFocalDispatch f1
      MREmptyGoal gamma2 delta2 <- positiveFocalDispatch f2
      return
        (MREmptyGoal (gamma1 <> gamma2) (delta1 <> delta2))

data ZetaXi :: (* -> *) -> (* -> *) -> ActCase -> * -> * -> * where
  FullZetaXi
    :: (cs a) -> (ORelFormula eb cs l a) -> ZetaXi eb cs FullXiEmptyResult l a
  EmptyZetaXi :: ZetaXi eb cs EmptyXiFullResult l a

{-| Left active relation, that is active relation of the form

      act(delta ; omega ===> Q)

    where xi is Q, hence a right-synchronous formula (and of course
    non-empty).

    Notice how the typeclass context enforces that the input formula is indeed
    right-synchronous. -}
leftActive
  :: (Eq a, Eq l, Eq (cs a), Ord l, Ord a)
  => (LCtxt eb cs l a)
  -> [ORelFormula eb cs l a]
  -> ZetaXi eb cs actcase l a
  -> Relation eb cs l a (MatchResult eb cs actcase l a)
  -- -> Relation l a (DerTerm l a, MatchResult actcase l a)
leftActive delta omega zetaxi =
  case omega of
    [] -> matchRel delta zetaxi
    (ORF (Conj f1 f2 _):rest) -> do
      res <- leftActive delta (ORF f2 : ORF f1 : rest) zetaxi
      return res
    (ORF fr@(Impl _ _ _ _ _):rest) -> leftActive (add (NF fr) delta) rest zetaxi
    (ORF fr@(Atom _):rest) -> leftActive (add (NF fr) delta) rest zetaxi

{-| Active match relation.
    It requires the input xi formula (if any) to be right-synchronous (otherwise
    we would have a right active relation). -}
matchRel
  :: (Eq a, Eq l, Eq (cs a), Ord l, Ord a)
  => (LCtxt eb cs l a)
  -> ZetaXi eb cs actcase l a
  -> Relation eb cs l a (MatchResult eb cs actcase l a)
  -- -> Relation l a (DerTerm l a, MatchResult actcase l a)
matchRel delta zetaxi =
  liftFun $ \inputSeq -> match schema inputSeq
  -- liftFun $ \(DER der inputSeq) -> fmap ((,) der) $ match schema inputSeq
  where
    schema =
      case zetaxi of
        EmptyZetaXi -> SSEmptyGoal delta
        FullZetaXi cs g -> SSFullGoal delta cs g

--------------------------------------------------------------------------------
-- Forward derived rules

focal
  :: (IsFocusable k, ControlSet cs a, Ord l, Ord a)
  => RelFormula eb cs k l a
  -> Relation eb cs l a (NeutralLabelledSequent eb cs l a)
focal formula = do
  (MREmptyGoal gamma delta) <- positiveFocalDispatch formula
  return $ NLS gamma delta mempty (ORF formula)

implLeft
  :: (BaseCtrl eb cs a, Ord l, Ord a)
  => RelFormula eb cs KImpl l a
  -> Relation eb cs l a (NeutralLabelledSequent eb cs l a)
implLeft fr@(Impl a _ cs b _) = do
  (MREmptyGoal gamma1 delta1) <- positiveFocalDispatch a
  (MRFullGoal gamma2 delta2 cs' concl) <-
    leftActive mempty [(ORF b)] EmptyZetaXi
  guard (respects (elemBaseAll delta2) cs)
  return $
    NLS (gamma1 <> gamma2) (add (NF fr) (delta1 <> delta2)) (cs <> cs') concl

copyRule
  :: (BaseCtrl eb cs a, Ord l, Ord a)
  => RelFormula eb cs KImpl l a
  -> Relation eb cs l a (NeutralLabelledSequent eb cs l a)
copyRule fr@(Impl a _ cs b _) = do
  (MREmptyGoal gamma1 delta1) <- positiveFocalDispatch a
  (MRFullGoal gamma2 delta2 cs' concl) <-
    leftActive mempty [(ORF b)] EmptyZetaXi
  guard (respects (elemBaseAll delta2) cs)
  return $
    NLS (add (ORF fr) (gamma1 <> gamma2)) (delta1 <> delta2) (cs <> cs') concl

implRight
  :: (BaseCtrl eb cs a, Ord l, Ord a)
  => RelFormula eb cs KImpl l a
  -> Relation eb cs l a (NeutralLabelledSequent eb cs l a)
implRight fr@(Impl a eb cs b _) = do
  (MREmptyGoal gamma delta) <-
    leftActive mempty [(ORF a)] (FullZetaXi cs (ORF b))
  guard ((elemBaseAll delta) == eb)
  return $ NLS gamma delta mempty (ORF fr)
