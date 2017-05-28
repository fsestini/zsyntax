{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module SimpleDerivationTerm (DerTerm(..), SimpleDerTerm, transitions) where

import TypeClasses (Pretty(..))
import Rules
import LFormula
import SFormula
import qualified Command.Structures as S (TransDerTerm(..))

instance (Ord a, Ord l) =>
         DerTerm (SimpleDerTerm a) (SrchFormula eb cty a l) where
  init = Init
  copy d ax = Copy d (stripDownAx ax)
  conjR d d' _ = ConjR d d'
  conjL d (reprConj -> CR f1 f2 _) = ConjL d (stripDown f1) (stripDown f2)
  implR d (reprImpl -> IR a _ _ _ _) = ImplR d (stripDown a)
  implL d d' (reprImpl -> IR _ _ _ b _) = ImplL d d' (stripDown b)

stripDownAx :: SrchAxiom cty a l -> SAxiom () a
stripDownAx (SrchAx ax) = SA . fmap (const ()) . mapCtyAx (const ()) $ ax

stripDown :: SrchFormula eb cs a l k -> SFormula () () a
stripDown (Srch f) = SF . fmap (const ()) . mapEbCty (const ()) (const ()) $ f

{-| Derivation term of the labelled forward sequent calculus. -}
data SimpleDerTerm a :: * where
  Init :: BioFormula a -> SimpleDerTerm a
  Copy :: SimpleDerTerm a -> SAxiom () a -> SimpleDerTerm a
  ConjR
    :: SimpleDerTerm a
    -> SimpleDerTerm a
    -> SimpleDerTerm a
  ConjL
    :: SimpleDerTerm a
    -> SFormula () () a
    -> SFormula () () a
    -> SimpleDerTerm a
  ImplR
    :: SimpleDerTerm a -> SFormula () () a -> SimpleDerTerm a
  ImplL
    :: SimpleDerTerm a
    -> SimpleDerTerm a
    -> SFormula () () a
    -> SimpleDerTerm a

deriving instance (Eq a, Ord a) => Eq (SimpleDerTerm a)
deriving instance Ord a => Ord (SimpleDerTerm a)

-- instance Pretty a => Pretty (SimpleDerTerm a) where
--   pretty (Init x) = "init(" ++ pretty x ++ ")"
--   pretty (Copy d a) = "copy(" ++ pretty d ++ "," ++ pretty a ++ ")"
--   pretty (ConjR d d') = "⊗R(" ++ pretty d ++ "," ++ pretty d' ++ ")"
--   pretty (ConjL d a b) = "⊗L(" ++ pretty d ++ "," ++ pretty a ++ "," ++ pretty b ++ ")"
--   pretty (ImplR d a) = "→R(" ++ pretty d ++ "," ++ pretty a ++ ")"
--   pretty (ImplL d d' b) = "→L(" ++ pretty d ++ "," ++ pretty d' ++ "," ++ pretty b ++ ")"

--------------------------------------------------------------------------------

conclusion :: SimpleDerTerm a -> SFormula () () a
conclusion (Init a) = sAtom a
conclusion (Copy d _) = conclusion d
conclusion (ConjR d d') = sConj (conclusion d) (conclusion d')
conclusion (ConjL d _ _) = conclusion d
conclusion (ImplR d a) = sImpl a () () (conclusion d)
conclusion (ImplL _ d' _) = conclusion d'

transitions :: SimpleDerTerm a -> [(SFormula () () a, SFormula () () a)]
transitions (Init _) = []
transitions (Copy d _) = transitions d
transitions (ConjR d1 d2) = transitions d1 ++ transitions d2
transitions (ConjL d _ _) = transitions d
transitions (ImplR d _) = transitions d
transitions (ImplL d1 d2 b) =
  transitions d1 ++ [(conclusion d1, b)] ++ transitions d2

newtype SimpleTransRepr a = STR (SFormula () () a, SFormula () () a)

instance Pretty a => Pretty (SimpleTransRepr a) where
  pretty (STR (from,to)) = pretty from ++ " --> " ++ pretty to

instance Pretty a => S.TransDerTerm (SimpleDerTerm a) where
  type TransRepr (SimpleDerTerm a) = SimpleTransRepr a
  transitions = fmap STR . SimpleDerivationTerm.transitions
