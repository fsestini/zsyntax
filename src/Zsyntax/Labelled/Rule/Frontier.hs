{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

module Zsyntax.Labelled.Rule.Frontier where
  -- ( GoalNSequent(..)
  -- , Rule
  -- , initialSequentsAndRules
  -- ) where

import Data.Maybe (mapMaybe)
import Otter (unRule, Subsumable(..))
import Data.MultiSet (MultiSet)
import Data.Foldable (toList)
import Data.Set (Set)
import qualified Data.Set as S (singleton, fromList)
import Data.Function (on)
import Control.Monad ((<=<))
import Data.Kind (Type)

import Zsyntax.Labelled.Rule.BipoleRelation
import Zsyntax.Labelled.Rule.Interface
import Zsyntax.Labelled.Formula
import Data.Bifunctor.Sum (Sum(..))
import Zsyntax.ReactionList (traverseSet, traverseMultiset)
import Control.Monad.Identity (Identity(..))

data DecoratedFormula :: Type -> Type -> Type where
  Unrestr :: LAxiom a l -> DecoratedFormula a l
  LinNeg :: LImpl a l -> DecoratedFormula a l
  LinPos :: LFormula a l -> DecoratedFormula a l

dfLabel :: DecoratedFormula a l -> Label a l
dfLabel (Unrestr ax) = Right (axLabel ax)
dfLabel (LinNeg f) = Right (implLabel f)
dfLabel (LinPos f) = label f

instance (Eq l, Eq a) => Eq (DecoratedFormula a l) where
  (==) = on (==) dfLabel

instance (Ord l, Ord a) => Ord (DecoratedFormula a l) where
  compare = on compare dfLabel

--------------------------------------------------------------------------------
-- Goal and result sequents.

-- | Type of goal sequents.
--
-- A goal sequent is characterized by an unrestricted context of axioms, a
-- (non-empty) neutral context, and a consequent formula of unspecified formula
-- kind (i.e., an opaque formula).
data GoalNSequent a l = GNS
  { _gnsUC :: Set (LAxiom a l)
  , _gnsLC :: MultiSet (Neutral a l) -- NonEmptyMultiSet (Neutral a l)
  , _gnsConcl :: LFormula a l -- Opaque (LFormula' cty l l)
  }
  deriving Show

traverseGNS :: (Applicative f, Ord l, Ord b) => (a -> f b) -> GoalNSequent a l -> f (GoalNSequent b l)
traverseGNS f (GNS uc lc c) =
  GNS <$> traverseSet (traverseAxiom f) uc
      <*> traverseMultiset (traverseNeutral f) lc
      <*> traverseAtoms f c

mapGNS :: (Ord l, Ord b) => (a -> b) -> GoalNSequent a l -> GoalNSequent b l
mapGNS f = runIdentity . traverseGNS (Identity . f)

instance (Ord a, Ord l) => Subsumable (GoalNSequent a l) where
  subsumes  (GNS uc lc fr) (GNS uc' lc' fr') =
    fr == fr' && lc == lc' && null (_scOnOnlyFirst (uc `subCtxtOf` uc'))

toGoalSequent :: LSequent a l -> GoalNSequent a l
toGoalSequent (LS uc lc _ c) = GNS uc lc c

--------------------------------------------------------------------------------
 -- Frontier computation

filterImpl :: [Neutral a l] -> [LImpl a l]
filterImpl = mapMaybe $ \case { L2 _ -> Nothing ; R2 i -> Just i }

frNeg :: (Ord l, Ord a) => Neutral a l -> Set (DecoratedFormula a l)
frNeg = \case { L2 _ -> mempty ; R2 (LImpl a _ _ b _) -> foc a <> act b }

frPos, foc, act :: (Ord l, Ord a) => LFormula a l -> Set (DecoratedFormula a l)
frPos f = case f of
  Atom _ -> mempty
  Conj {} -> foc f
  Impl a _ _ b _ -> mconcat [act a, frPos b, S.singleton (LinPos b)]
foc f = case f of
  Atom _ -> mempty
  Conj a b _ -> foc a <> foc b
  Impl {} -> S.singleton (LinPos f) <> frPos f
act =
  foldLSum (const mempty) (\(LConj f1 f2 _) -> act f1 <> act f2)
           (\i -> S.singleton (LinNeg i) <> frPos (injImpl i))

-- | Computes the frontier of a sequent.
frontier :: (Ord l, Ord a) => GoalNSequent a l -> Set (DecoratedFormula a l)
frontier (GNS uc lc fgoal) =
  mconcat
    [ toplevelUC, toplevelLC
    , ucFrontier, linFrontier
    , goalFrontier, S.singleton (LinPos fgoal)
    ]
  where
    lcList = toList lc
    toplevelUC = S.fromList . map Unrestr . toList $ uc
    toplevelLC = S.fromList . fmap LinNeg . filterImpl $ lcList
    ucFrontier = mconcat . fmap (frNeg . R2 . axToFormula) . toList $ uc
    linFrontier = mconcat . fmap frNeg $ lcList
    goalFrontier = frPos fgoal

--------------------------------------------------------------------------------
-- Generation of initial rules from the frontier.

generateRule :: (Ord a, Ord l) => DecoratedFormula a l -> BipoleRule a l
generateRule (Unrestr axiom) = copyRule axiom
generateRule (LinNeg impl) = implLeft impl
generateRule (LinPos f) = foldLSum (focus . L2) (focus . R2) implRight f

--------------------------------------------------------------------------------
-- Main function

-- | Type of proper rules of the formal system, i.e. 'BipoleRule's that take at
-- least one premise.
type ProperRule a l = AnnLSequent a l -> BipoleRule a l

-- | Computes the set of initial rules from the frontier of a specified goal
-- sequent.
initialRules :: (Ord a, Ord l) => GoalNSequent a l -> [BipoleRule a l]
initialRules = fmap generateRule . toList . frontier

mayProperRule :: BipoleRule a l -> Maybe (ProperRule a l)
mayProperRule = either (const Nothing) Just <=< unRule

maySequent :: BipoleRule a l -> Maybe (AnnLSequent a l)
maySequent = either Just (const Nothing) <=< unRule
