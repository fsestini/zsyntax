{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module DerivationTerm where

import Formula
import SFormula

{-| Derivation term of the labelled forward sequent calculus. -}
data DerTerm l a :: * where
  {- init(p) :: . ; p # p ---> p -}
  Init :: BioFormula a -> DerTerm l a

  {-
        D :: G, D, l # A ---> C
    ---------------------------------
    copy(D, l # A) :: G+l#A ; D ---> C
  -}
  Copy :: DerTerm l a -> Label l a -> SFormula a -> DerTerm l a

  {-
        D :: G, D ---> A      D' :: G', D' ---> B
     -----------------------------------------------
     oR(D, D' ; r # A o B) :: G+G'; D, D' ---> A o B
  -}
  ConjR :: DerTerm l a -> DerTerm l a -> l -> DerTerm l a

  {-
                  D :: G, D, l1 # A, l2 # B ---> C
     ----------------------------------------------------------
     oL(D, l1 # A, l2 # B, l # A o B) :: G, D, l # A o B ---> C
  -}
  ConjL
    :: DerTerm l a
    -> Label l a
    -> SFormula a
    -> Label l a
    -> SFormula a
    -> l
    -> DerTerm l a

  {-
             D :: G, D, l # A ---> B
    ----------------------------------------------
    -oR(D, l # A ; r # A -o B) :: G, D ---> A -o B
  -}
  ImplR :: DerTerm l a -> Label l a -> SFormula a -> l -> DerTerm l a

  {-
        D :: G, D ---> r # A       D' :: G', D', l # B ---> C
    -----------------------------------------------------------------
    -oL(D, D', l # B ; s # A -o B) :: G+G' ; D, D', s # A -o B ---> C
  -}
  ImplL
    :: DerTerm l a -- D
    -> DerTerm l a -- D'
    -> Label l a
    -> SFormula a
    -> l -- s
    -> DerTerm l a
