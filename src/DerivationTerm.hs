{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module DerivationTerm (DerTerm(..), SimpleDerTerm, transitions) where

import RelFormula
import SFormula

class DerTerm term eb cs a l where
  init :: BioFormula a -> term
  copy :: term -> Axiom eb cs a l -> term
  conjR :: term -> term -> LFormula eb cs KConj a l -> term
  conjL :: term -> LFormula eb cs KConj a l -> term
  implR :: term -> ImplFormula eb cs IRegular a l -> term
  implL :: term -> term -> ImplFormula eb cs IRegular a l -> term

instance DerTerm (SimpleDerTerm a) eb cs a l where
  init = Init
  copy d ax = Copy d (fromLAxiom (mapEbCsI mapU mapU $ ax))
  conjR d d' _ = ConjR d d'
  conjL d (Conj f1 f2 _) = ConjL d (stripDown f1) (stripDown f2)
  implR d (ImplF a _ _ _ _) = ImplR d (stripDown a)
  implL d d' (ImplF _ _ _ b _) =
    ImplL d d' (fromLFormula (mapEbCsF mapU mapU b))

data U a = U deriving (Eq, Ord)

mapU :: f a -> U a
mapU = const U

stripDown :: LFormula eb cs k a l -> SFormula U U a
stripDown = fromLFormula . mapEbCsF mapU mapU

{-| Derivation term of the labelled forward sequent calculus. -}
data SimpleDerTerm a :: * where
  Init :: BioFormula a -> SimpleDerTerm a
  Copy :: SimpleDerTerm a -> SAxiom U U a -> SimpleDerTerm a
  ConjR
    :: SimpleDerTerm a
    -> SimpleDerTerm a
    -> SimpleDerTerm a
  ConjL
    :: SimpleDerTerm a
    -> SFormula U U a
    -> SFormula U U a
    -> SimpleDerTerm a
  ImplR
    :: SimpleDerTerm a -> SFormula U U a -> SimpleDerTerm a
  ImplL
    :: SimpleDerTerm a
    -> SimpleDerTerm a
    -> SFormula U U a
    -> SimpleDerTerm a

deriving instance (Eq a, Ord a) => Eq (SimpleDerTerm a)
deriving instance Ord a => Ord (SimpleDerTerm a)

instance Show a => Show (SimpleDerTerm a) where
  show (Init x) = "init(" ++ show x ++ ")"
  show (Copy d a) = "copy(" ++ show d ++ "," ++ show a ++ ")"
  show (ConjR d d') = "⊗R(" ++ show d ++ "," ++ show d' ++ ")"
  show (ConjL d a b) = "⊗L(" ++ show d ++ "," ++ show a ++ "," ++ show b ++ ")"
  show (ImplR d a) = "→R(" ++ show d ++ "," ++ show a ++ ")"
  show (ImplL d d' b) = "→L(" ++ show d ++ "," ++ show d' ++ "," ++ show b ++ ")"

--------------------------------------------------------------------------------

conclusion :: SimpleDerTerm a -> SFormula U U a
conclusion (Init a) = sAtom a
conclusion (Copy d _) = conclusion d
conclusion (ConjR d d') = sConj (conclusion d) (conclusion d')
conclusion (ConjL d _ _) = conclusion d
conclusion (ImplR d a) = sImpl a U U (conclusion d)
conclusion (ImplL _ d' _) = conclusion d'

transitions :: SimpleDerTerm a -> [(SFormula U U a, SFormula U U a)]
transitions (Init _) = []
transitions (Copy d _) = transitions d
transitions (ConjR d1 d2) = transitions d1 ++ transitions d2
transitions (ConjL d _ _) = transitions d
transitions (ImplR d _) = transitions d
transitions (ImplL d1 d2 b) =
  transitions d1 ++ [(conclusion d1, b)] ++ transitions d2
