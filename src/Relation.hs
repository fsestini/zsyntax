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
  , focus
  , implLeft
  , copyRule
  , implRight
  , Rule
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
import ForwardSequent
import LinearContext
{-import TypeClasses-}

--------------------------------------------------------------------------------

-- | Type of labelled sequents decorated with derivation terms
data DLSequent term eb cs a l = DLS
  { derivation :: term
  , sequent :: NeutralSequent eb cs a l
  } deriving (Eq, Ord)

instance (Ord l, Ord a, Eq (cs a)) =>
         ForwardSequent (DLSequent term eb cs a l) where
  subsumes (DLS _ s1) (DLS _ s2) = subsumes s1 s2

-- instance Coercible (DLSequent a l) (LabelledSequent a l) where
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
-- type Relation a l b = Rel (DLSequent a l) b
type Relation eb cs a l b = Rel (NeutralSequent eb cs a l) b

--------------------------------------------------------------------------------
-- Sequent schemas.

-- | Type of linear contexts which appear in sequent schemas.
newtype SchemaLCtxt eb cs a l = SLC (LCtxt eb cs a l)

matchLinearCtxt
  :: (MonadFail m, Ord a, Ord l)
  => SchemaLCtxt eb cs a l -> LCtxt eb cs a l -> m (LCtxt eb cs a l)
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
  SSEmptyGoal :: (LCtxt eb cs a l) -> SequentSchema eb cs EmptyXiFullResult a l
  SSFullGoal
    :: (LCtxt eb cs a l)
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

{-| Matches a labelled sequent against an act sequent schema.
    Returns the result in a MonadFail instance, which signals the error in case
    the match fails. -}
match
  :: (Eq a, Eq l, Eq (cs a), MonadFail m, Alternative m, Ord a, Ord l)
  => SequentSchema eb cs ac a l
  -> NeutralSequent eb cs a l
  -> m (MatchResult eb cs ac a l)
match (SSEmptyGoal delta) (NS gamma delta' cs goal) = do
  delta'' <- matchLinearCtxt (SLC delta) delta'
  return $ MRFullGoal gamma delta'' cs goal
match (SSFullGoal delta cs goal) (NS gamma delta' cs' goal') =
  guard (goal == goal') >> guard (cs == cs') >>
  MREmptyGoal gamma <$> matchLinearCtxt (SLC delta) delta'

type FocMatchRes eb cs a l = MatchResult eb cs FullXiEmptyResult a l

{-| Positive focal relation.
    The fact that it returns a result sequent with empty goal is statically
    enforced by the type of the function. -}
positiveFocalDispatch
  :: (Monoid (cs a), Eq a, Eq (cs a), Eq l, Ord l, Ord a)
  => LFormula eb cs k a l -> Relation eb cs a l (FocMatchRes eb cs a l)
positiveFocalDispatch formula =
  case formula of
    Atom _ -> return (MREmptyGoal mempty (singletonCtxt (NF formula)))
    Impl _ _ _ _ _ -> liftFun $ \inputSeq -> match schema inputSeq
      where schema = SSFullGoal mempty mempty (OLF formula)
    Conj f1 f2 r -> do
      MREmptyGoal gamma1 delta1 <- positiveFocalDispatch f1
      MREmptyGoal gamma2 delta2 <- positiveFocalDispatch f2
      return
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
  :: (Eq a, Eq l, Eq (cs a), Ord l, Ord a)
  => (LCtxt eb cs a l)
  -> [OLFormula eb cs a l]
  -> ZetaXi eb cs actcase a l
  -> Relation eb cs a l (MatchResult eb cs actcase a l)
  -- -> Relation a l (DerTerm a l, MatchResult actcase a l)
leftActive delta omega zetaxi =
  case omega of
    [] -> matchRel delta zetaxi
    (OLF (Conj f1 f2 _):rest) -> do
      res <- leftActive delta (OLF f2 : OLF f1 : rest) zetaxi
      return res
    (OLF fr@(Impl _ _ _ _ _):rest) -> leftActive (add (NF fr) delta) rest zetaxi
    (OLF fr@(Atom _):rest) -> leftActive (add (NF fr) delta) rest zetaxi

{-| Active match relation.
    It requires the input xi formula (if any) to be right-synchronous (otherwise
    we would have a right active relation). -}
matchRel
  :: (Eq a, Eq l, Eq (cs a), Ord l, Ord a)
  => (LCtxt eb cs a l)
  -> ZetaXi eb cs actcase a l
  -> Relation eb cs a l (MatchResult eb cs actcase a l)
  -- -> Relation a l (DerTerm a l, MatchResult actcase a l)
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

type Rule eb cs a l = Relation eb cs a l (NeutralSequent eb cs a l)

focus
  :: (IsFocusable k, ControlSet cs a, Ord l, Ord a)
  => LFormula eb cs k a l
  -> Relation eb cs a l (NeutralSequent eb cs a l)
focus formula = do
  (MREmptyGoal gamma delta) <- positiveFocalDispatch formula
  return $ NS gamma delta mempty (OLF formula)

implLeft
  :: (BaseCtrl eb cs a, Ord l, Ord a)
  => ImplFormula eb cs IRegular a l
  -> Relation eb cs a l (NeutralSequent eb cs a l)
implLeft fr@(ImplF a _ cs b _) = do
  (MREmptyGoal gamma1 delta1) <- positiveFocalDispatch a
  (MRFullGoal gamma2 delta2 cs' concl) <-
    leftActive mempty [(OLF b)] EmptyZetaXi
  guard (respects (elemBaseAll delta2) cs)
  return $
    NS (gamma1 <> gamma2) (add (NF (Impl' fr)) (delta1 <> delta2)) (cs <> cs') concl

copyRule
  :: (BaseCtrl eb cs a, Ord l, Ord a)
  => Axiom eb cs a l
  -> Relation eb cs a l (NeutralSequent eb cs a l)
copyRule fr@(ImplF a EmptySpot cs b _) = do
  (MREmptyGoal gamma1 delta1) <- positiveFocalDispatch a
  (MRFullGoal gamma2 delta2 cs' concl) <-
    leftActive mempty [(OLF b)] EmptyZetaXi
  guard (respects (elemBaseAll delta2) cs)
  return $
    NS (add fr (gamma1 <> gamma2)) (delta1 <> delta2) (cs <> cs') concl

implRight
  :: (BaseCtrl eb cs a, Ord l, Ord a)
  => ImplFormula eb cs IRegular a l
  -> Relation eb cs a l (NeutralSequent eb cs a l)
implRight fr@(ImplF a (FullSpot eb) cs b _) = do
  (MREmptyGoal gamma delta) <-
    leftActive mempty [(OLF a)] (FullZetaXi cs (OLF b))
  guard ((elemBaseAll delta) == eb)
  return $ NS gamma delta mempty (OLF (Impl' fr))
