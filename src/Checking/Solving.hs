module Checking.Solving (solveDerivation) where

import Control.Monad ((>=>))
import Control.Monad.Fail (MonadFail)
import Checking.Constraints
import Checking.Generation
import Checking.DerivationTerm
import qualified Data.Set as S (null, intersection)
import Formula

solveAll :: Ord a => [BioConstraint l a] -> Bool
solveAll = and . map solve

solve :: Ord a => BioConstraint l a -> Bool
solve (Respect bss (Sum css1 css2)) =
  solveAll [Respect bss css1, Respect bss css2]
solve (Respect (Sum bss1 bss2) css) =
  solveAll [Respect bss1 css, Respect bss2 css]
solve (Respect (Set set1) (Set set2)) =
  S.null (S.intersection (bsAsSet set1) (csAsSet set2))

instantiateSchema :: s -> Schema s l -> Schema s l
instantiateSchema set sch =
  case sch of
    Label _ -> sch
    Sum sch1 sch2 ->
      Sum (instantiateSchema set sch1) (instantiateSchema set sch2)
    x@(Set _) -> x

instantiate
  :: (Ord l, Ord a)
  => BioConstraint l a -> BioConstraint l a
instantiate (Respect bss css) =
  Respect (instantiateSchema mempty bss) (instantiateSchema mempty css)
instantiate (And c1 c2) = And (instantiate c1) (instantiate c2)
instantiate (Or c1 c2) = Or (instantiate c1) (instantiate c2)

solveDerivation
  :: (Ord a, Ord l, MonadFail (m l a), ConstraintMonad m l a)
  => DerTerm l a -> m l a Bool
solveDerivation = generateConstraints >=> return . solveAll
