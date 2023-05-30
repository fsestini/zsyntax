{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}

module Zsyntax.Labelled.Rule.Frontier where
  -- ( GoalNSequent(..)
  -- , Rule
  -- , initialSequentsAndRules
  -- ) where

import Data.Maybe (mapMaybe)
import Data.Constraint (Dict(..))
import Otter (unRule, Subsumable(..))
import Data.MultiSet (MultiSet)
import Data.Foldable (toList)
import Data.Set (Set)
import qualified Data.Set as S (singleton, fromList)
import Data.Function (on)
import Control.Monad (join)
import Data.Kind (Type)

import Zsyntax.Labelled.Rule.BipoleRelation
import Zsyntax.Labelled.Rule.Interface
import Zsyntax.Labelled.Formula

data DecoratedFormula :: Type -> Type -> Type where
  Unrestr :: LAxiom a l -> DecoratedFormula a l
  LinNeg :: LFormula KImpl a l -> DecoratedFormula a l
  LinPos :: Opaque a l -> DecoratedFormula a l

dfLabel :: DecoratedFormula a l -> Label a l
dfLabel (Unrestr ax) = L (axLabel ax)
dfLabel (LinNeg f) = label f
dfLabel (LinPos (O f)) = label f

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
  , _gnsConcl :: Opaque a l -- Opaque (LFormula' cty l l)
  }
  deriving Show

instance (Ord a, Ord l) => Subsumable (GoalNSequent a l) where
  subsumes  (GNS uc lc fr) (GNS uc' lc' fr') =
    fr == fr' && lc == lc' && null (_scOnOnlyFirst (uc `subCtxtOf` uc'))

toGoalSequent :: LSequent a l -> GoalNSequent a l
toGoalSequent (LS uc lc _ c) = GNS uc lc c

--------------------------------------------------------------------------------
 -- Frontier computation

filterImpl :: [Neutral a l] -> [LFormula 'KImpl a l]
filterImpl = mapMaybe aux
  where
    aux :: Neutral a l -> Maybe (LFormula 'KImpl a l)
    aux (N (f :: LFormula k a l)) =
      either (const Nothing) (\Dict -> Just f) (decideNeutral @k)

frNeg :: (Ord l, Ord a) => Neutral a l -> Set (DecoratedFormula a l)
frNeg = switchN (const mempty) (\(Impl a _ _ b _) -> foc a <> act b)

frPos, foc, act :: (Ord l, Ord a) => LFormula k a l -> Set (DecoratedFormula a l)
frPos f = case f of
  Atom _ -> mempty
  Conj {} -> foc f
  Impl a _ _ b _ -> mconcat [act a, frPos b, S.singleton (LinPos (O b))]
foc f = case f of
  Atom _ -> mempty
  Conj a b _ -> foc a <> foc b
  Impl {} -> S.singleton (LinPos (O f)) <> frPos f
act f = case f of
  Atom _ -> mempty
  Conj f1 f2 _ -> act f1 <> act f2
  Impl {} -> S.singleton (LinNeg f) <> frPos f

-- | Computes the frontier of a sequent.
frontier :: (Ord l, Ord a) => GoalNSequent a l -> Set (DecoratedFormula a l)
frontier (GNS uc lc goal@(O fgoal)) =
  mconcat 
    [ toplevelUC, toplevelLC
    , ucFrontier, linFrontier
    , goalFrontier, S.singleton (LinPos goal)
    ]
  where
    lcList = toList lc
    toplevelUC = S.fromList . map Unrestr . toList $ uc
    toplevelLC = S.fromList . fmap LinNeg . filterImpl $ lcList
    ucFrontier = mconcat . fmap (frNeg . N . axToFormula) . toList $ uc
    linFrontier = mconcat . fmap frNeg $ lcList
    goalFrontier = frPos fgoal

--------------------------------------------------------------------------------
-- Generation of initial rules from the frontier.

generateRule :: (Ord a, Ord l) => DecoratedFormula a l -> BipoleRule a l
generateRule (Unrestr axiom) = copyRule axiom
generateRule (LinNeg impl) = implLeft impl
generateRule (LinPos (O f)) =
  case f of { Atom _ -> focus f ; Conj {} -> focus f ; Impl {} -> implRight f }
  
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
mayProperRule = join . fmap (either (const Nothing) Just) . unRule

maySequent :: BipoleRule a l -> Maybe (AnnLSequent a l)
maySequent = join . fmap (either Just (const Nothing)) . unRule
