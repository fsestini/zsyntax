{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

{-| Module of derived rule relations. -}

module Zsyntax.Labelled.Rule.BipoleRelation where
  -- ( (:::)
  -- , AnnLSequent
  -- , IsFocusable
  -- , BipoleRule
  -- , focus
  -- , implLeft
  -- , copyRule
  -- , implRight
  -- ) where

import Data.Function (on)
import Data.Bifunctor (Bifunctor(..))
import Control.Monad (guard)

import Otter
import Data.Set (insert)
import Data.MultiSet (MultiSet, isSubsetOf, (\\), singleton)
import qualified Data.MultiSet as MS (insert)

import Zsyntax.Labelled.Rule.Interface
import Zsyntax.Labelled.Formula
import Zsyntax.Labelled.DerivationTerm
import Zsyntax.ReactionList

respects :: Ord a => ElemBase a -> RList (ElemBase a) (CtrlSet a) -> Bool
respects = respectsRList (\eb cty -> msRespectsCS (unEB eb) cty)

--------------------------------------------------------------------------------

-- | Type of derivation terms-decorated data.
data tm ::: pl = (:::) { _term :: tm, _payload :: pl } deriving (Eq, Ord, Show)

instance Bifunctor (:::) where
  bimap f g (x ::: y) = f x ::: g y

-- | Type of labelled sequents that are annotated with a derivation term.
type AnnLSequent a l = DerivationTerm a l ::: LSequent a l

-- | A relation is an unbounded curried function with an annotated sequents as
-- input.
type BipoleRel a l = Rule (AnnLSequent a l)

-- | A rule of the derived rule calculus is a relation that has
-- derivation term-decorated sequents as both input and output.
type BipoleRule a l = Rule (AnnLSequent a l) (AnnLSequent a l)

-- | Predicate identifying those formula kinds that correspond to focusable
-- formulas.
class IsFocusable (k :: FKind) where
instance IsFocusable KAtom where
instance IsFocusable KConj where

type FocMatchRes a l = MatchRes a l FullXiEmptyResult
type DTFocMatchRes a l = DerivationTerm a l ::: FocMatchRes a l
type DTMatchRes a l actcase = DerivationTerm a l ::: MatchRes a l actcase

instance Subsumable s => Subsumable (tm ::: s) where
  subsumes = subsumes `on` _payload

--------------------------------------------------------------------------------

-- | Given two multisets m1 and m2, it checks whether m1 is contained in m2,
-- and returns the rest of m2 if it is the case.
matchMultiSet :: Ord a => MultiSet a -> MultiSet a -> Maybe (MultiSet a)
matchMultiSet m1 m2 = if isSubsetOf m1 m2 then Just (m2 \\ m1) else Nothing

matchLinearCtxt :: (Ord a, Ord l) => SchemaLCtxt a l -> LCtxt a l -> Maybe (LCtxt a l)
matchLinearCtxt (SLC slc) = matchMultiSet slc

matchSchema :: (Ord a, Ord l)
      => SSchema a l act -> AnnLSequent a l -> Maybe (DTMatchRes a l act)
matchSchema (SSEmptyGoal delta) (term ::: LS gamma delta' cty goal) = do
  delta'' <- matchLinearCtxt delta delta'
  pure (term ::: MRFullGoal gamma delta'' cty goal)
matchSchema (SSFullGoal delta cty cncl) (tm ::: LS gamma delta' cty' cncl') = do
  delta'' <- matchLinearCtxt delta delta'
  guard (cty == cty')
  guard (cncl == cncl')
  pure (tm ::: MREmptyGoal gamma delta'')

matchRel :: (Ord a, Ord l)
         => LCtxt a l -> ZetaXi a l act -> BipoleRel a l (DTMatchRes a l act)
matchRel delta zetaxi = match . matchSchema $
  case zetaxi of
    EmptyZetaXi -> SSEmptyGoal (SLC delta)
    FullZetaXi cty g -> SSFullGoal (SLC delta) cty g

positiveFocalDispatch
  :: (Ord l, Ord a)
  => LFormula k a l
  -> BipoleRel a l (DTFocMatchRes a l)
positiveFocalDispatch fr = case fr of
  Atom a -> pure (Init a ::: MREmptyGoal mempty (singleton (N fr)))
  Impl {} -> match (matchSchema (SSFullGoal (SLC mempty) mempty (O fr)))
  Conj f1 f2 l -> do
    d ::: MREmptyGoal g1 d1 <- positiveFocalDispatch f1
    d' ::: MREmptyGoal g2 d2 <- positiveFocalDispatch f2
    pure $ ConjR d d' l ::: MREmptyGoal (g1 <> g2) (d1 <> d2)

leftActive
  :: (Ord l, Ord a) => LCtxt a l -> [Opaque a l] -> ZetaXi a l act
  -> BipoleRel a l (DTMatchRes a l act)
leftActive delta [] zetaxi = matchRel delta zetaxi
leftActive delta (O f : rest) zetaxi = withMaybeNeutral f
  (leftActive (MS.insert (N f) delta) rest zetaxi)
  (\(Conj f1 f2 _) -> do
      d ::: res <- leftActive delta (O f2 : O f1 : rest) zetaxi
      pure $ ConjL d ::: res)

focus :: (Ord l, Ord a, IsFocusable k) => LFormula k a l -> BipoleRule a l
focus formula = do
  d ::: MREmptyGoal gamma delta <- positiveFocalDispatch formula
  pure (d ::: LS gamma delta mempty (O formula))

implLeft :: (Ord l, Ord a) => LFormula KImpl a l -> BipoleRule a l
implLeft fr@(Impl f1 _ cty f2 _) = do
  d  ::: MREmptyGoal g1 d1 <- positiveFocalDispatch f1
  d' ::: MRFullGoal g2 d2 cty' cl <- leftActive mempty [(O f2)] EmptyZetaXi
  let b = lcBase d2
      ext = extend b cty
  guard (respects b cty)
  pure $ ImplL d d' f2
     ::: LS (g1 <> g2) (MS.insert (N fr) (d1 <> d2)) (ext <> cty') cl

copyRule :: (Ord a, Ord l) => LAxiom a l -> BipoleRule a l
copyRule ax = let fr = axToFormula ax in case fr of
  Impl f1 _ cty f2 _ -> do
    d  ::: MREmptyGoal g1 d1 <- positiveFocalDispatch f1
    d' ::: MRFullGoal g2 d2 cty' cl <- leftActive mempty [(O f2)] EmptyZetaXi
    let b = lcBase d2 ; ext = extend b cty
    guard (respects b cty)
    pure $ Copy (ImplL d d' f2) ax
       ::: LS (insert ax (g1 <> g2)) (d1 <> d2) (ext <> cty') cl

implRight :: (Ord a, Ord l) => LFormula KImpl a l -> BipoleRule a l
implRight fr@(Impl f1 eb cty f2 l) = do
  tm ::: MREmptyGoal g d <- leftActive mempty [(O f1)] (FullZetaXi cty (O f2))
  guard (lcBase d == eb)
  pure $ ImplR tm fr eb cty l ::: LS g d mempty (O fr)
