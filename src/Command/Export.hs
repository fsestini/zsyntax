module Command.Export (ppAxEnv, ppThrmEnv) where

import RelFormula (bfToAtoms, BioFormula(..))
import SFormula (SAxiom(..), ImplFormula(..))
import Command.Structures
       (ThrmName(..), SA, QueriedSeq(..), AxiomsString(..), AxEnv,
        ThrmEnv, FEnv(..))
import Data.List (intersperse)
import Checking (ctrlToList)
import Data.Bifunctor (first, second)

exportAxiom :: ThrmName -> SA -> String
exportAxiom (TN name) (SA (ImplF from _ cs to _)) =
  "add axiom " ++ name ++ " (" ++ aux aggr1 ++ ") (" ++ aux aggr2
  ++ ") unless (" ++ (aux . ctrlToList $ cs) ++ ")"
  where
    aggr1 = bfToAtoms from
    aggr2 = bfToAtoms to
    aux = concat . intersperse "," . fmap ppBioFormula

ppBioFormula :: BioFormula String -> String
ppBioFormula (BioAtom x) = x
ppBioFormula (BioInter x y) = ppBioFormula x ++ " <> " ++ ppBioFormula y

exportTheorem :: ThrmName -> QueriedSeq -> String
exportTheorem (TN name) (QS (AS axStr) fromStr toStr) =
  "query " ++ name ++ " (" ++ fromStr ++ ") (" ++ toStr ++ ") with axioms ("
  ++ axStr ++ ")"

ppAxEnv :: AxEnv -> [String]
ppAxEnv = fmap (uncurry exportAxiom) . feAsList

ppThrmEnv :: ThrmEnv -> [String]
ppThrmEnv = fmap (uncurry exportTheorem . second fst) . feAsList
