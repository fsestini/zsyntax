{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module Zsyntax.Labelled.DerivationTerm where

import Zsyntax.Labelled.Formula
import Control.Monad.Identity (Identity(runIdentity, Identity))

-- | Derivation term of the labelled forward sequent calculus.
data DerivationTerm a l where
  Init  :: a -> DerivationTerm a l
  Copy  :: DerivationTerm a l -> LAxiom a l -> DerivationTerm a l
  ConjR :: DerivationTerm a l -> DerivationTerm a l -> l -> DerivationTerm a l
  ConjL :: DerivationTerm a l -> DerivationTerm a l
  ImplR :: DerivationTerm a l -> LFormula a l -> ElemBase a -> ReactionList a -> l
        -> DerivationTerm a l
  ImplL :: DerivationTerm a l -> DerivationTerm a l -> LFormula a l
        -> DerivationTerm a l

deriving instance Functor (DerivationTerm a)

mapDerivationTerm :: Ord b => (a -> b) -> DerivationTerm a l -> DerivationTerm b l
mapDerivationTerm f = runIdentity . traverseDerivationTerm (Identity . f)

traverseDerivationTerm
  :: (Applicative f, Ord b)
  => (a -> f b) -> DerivationTerm a l -> f (DerivationTerm b l)
traverseDerivationTerm f = \case
  Init x -> Init <$> f x
  Copy d a -> Copy <$> traverseDerivationTerm f d <*> traverseAxiom f a
  ConjR d d' l ->
    ConjR <$> traverseDerivationTerm f d <*> traverseDerivationTerm f d' <*> pure l
  ConjL d -> ConjL <$> traverseDerivationTerm f d
  ImplR d i b r l ->
    ImplR <$> traverseDerivationTerm f d <*> traverseAtoms f i
          <*> traverseElemBase f b <*> traverseRL f r <*> pure l
  ImplL d d' i ->
    ImplL <$> traverseDerivationTerm f d
          <*> traverseDerivationTerm f d'
          <*> traverseAtoms f i

concl :: DerivationTerm a l -> LFormula a l
concl (Init a) = Atom a
concl (Copy d _) = concl d
concl (ConjR d d' l) = Conj (concl d) (concl d') l
concl (ConjL d) = concl d
concl (ImplR d a eb cty l) = Impl a eb cty (concl d) l
concl (ImplL _ d' _) = concl d'

transitions :: DerivationTerm a l -> [(LFormula a l, LFormula a l)]
transitions (Init _) = []
transitions (Copy d _) = transitions d
transitions (ConjR d1 d2 _) = transitions d1 ++ transitions d2
transitions (ConjL d) = transitions d
transitions (ImplR d _ _ _ _) = transitions d
transitions (ImplL d1 d2 b) = transitions d1 ++ [(concl d1, b)] ++ transitions d2
