{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module DerivationTerm where

-- import Formula
import RelFormula

class DerTerm term eb cs a l where
  init :: BioFormula a -> term
  copy :: term -> Axiom eb cs a l -> term
  conjR :: term -> term -> LFormula eb cs KConj a l -> term
  conjL :: term -> LFormula eb cs KConj a l -> term
  implR :: term -> ImplFormula eb cs IRegular a l -> term
  implL :: term -> term -> ImplFormula eb cs IRegular a l -> term

instance DerTerm (SimpleDerTerm eb cs a l) eb cs a l where
  init = Init
  copy = Copy
  conjR = ConjR
  conjL = ConjL
  implR = ImplR
  implL = ImplL

getTransitions :: SimpleDerTerm eb cs a l -> [ImplFormula eb cs IRegular a l]
getTransitions (Init _) = []
getTransitions (Copy d _) = getTransitions d
getTransitions (ConjR d1 d2 _) = getTransitions d1 ++ getTransitions d2
getTransitions (ConjL d _) = getTransitions d
getTransitions (ImplR d _) = getTransitions d
getTransitions (ImplL d1 d2 impl) =
  getTransitions d1 ++ [impl] ++ getTransitions d2

{-| Derivation term of the labelled forward sequent calculus. -}
data SimpleDerTerm eb cs a l :: *
  {- init(p) :: . ; p # p ---> p -}
      where
  Init :: BioFormula a -> SimpleDerTerm eb cs a l
  {-
        D :: G, D, l # A ---> C
    ---------------------------------
    copy(D, l # A) :: G+l#A ; D ---> C
  -}
  Copy :: SimpleDerTerm eb cs a l -> Axiom eb cs a l -> SimpleDerTerm eb cs a l
  {-
        D :: G, D ---> A      D' :: G', D' ---> B
     -----------------------------------------------
     oR(D, D' ; r # A o B) :: G+G'; D, D' ---> A o B
  -}
  ConjR
    :: SimpleDerTerm eb cs a l
    -> SimpleDerTerm eb cs a l
    -> LFormula eb cs KConj a l
    -> SimpleDerTerm eb cs a l
  {-
                  D :: G, D, l1 # A, l2 # B ---> C
     ----------------------------------------------------------
     oL(D, l1 # A, l2 # B, l # A o B) :: G, D, l # A o B ---> C
  -}
  ConjL
    :: SimpleDerTerm eb cs a l
    -> LFormula eb cs KConj a l
    -> SimpleDerTerm eb cs a l
  {-
             D :: G, D, l # A ---> B
    ----------------------------------------------
    -oR(D, l # A ; r # A -o B) :: G, D ---> A -o B
  -}
  ImplR
    :: SimpleDerTerm eb cs a l
    -> ImplFormula eb cs IRegular a l
    -> SimpleDerTerm eb cs a l
  {-
        D :: G, D ---> r # A       D' :: G', D', l # B ---> C
    -----------------------------------------------------------------
    -oL(D, D', l # B ; s # A -o B) :: G+G' ; D, D', s # A -o B ---> C
  -}
  ImplL
    :: SimpleDerTerm eb cs a l -- D
    -> SimpleDerTerm eb cs a l -- D'
    -> ImplFormula eb cs IRegular a l
    -> SimpleDerTerm eb cs a l
  deriving (Eq, Ord, Show)


-- {-| Derivation term of the labelled forward sequent calculus. -}
-- data DerTerm l a :: * where
--   {- init(p) :: . ; p # p ---> p -}
--   Init :: BioFormula a -> DerTerm l a

--   {-
--         D :: G, D, l # A ---> C
--     ---------------------------------
--     copy(D, l # A) :: G+l#A ; D ---> C
--   -}
--   Copy :: DerTerm l a -> Label l a -> SFormula a -> DerTerm l a

--   {-
--         D :: G, D ---> A      D' :: G', D' ---> B
--      -----------------------------------------------
--      oR(D, D' ; r # A o B) :: G+G'; D, D' ---> A o B
--   -}
--   ConjR :: DerTerm l a -> DerTerm l a -> l -> DerTerm l a

--   {-
--                   D :: G, D, l1 # A, l2 # B ---> C
--      ----------------------------------------------------------
--      oL(D, l1 # A, l2 # B, l # A o B) :: G, D, l # A o B ---> C
--   -}
--   ConjL
--     :: DerTerm l a
--     -> Label l a
--     -> SFormula a
--     -> Label l a
--     -> SFormula a
--     -> l
--     -> DerTerm l a

--   {-
--              D :: G, D, l # A ---> B
--     ----------------------------------------------
--     -oR(D, l # A ; r # A -o B) :: G, D ---> A -o B
--   -}
--   ImplR :: DerTerm l a -> Label l a -> SFormula a -> l -> DerTerm l a

--   {-
--         D :: G, D ---> r # A       D' :: G', D', l # B ---> C
--     -----------------------------------------------------------------
--     -oL(D, D', l # B ; s # A -o B) :: G+G' ; D, D', s # A -o B ---> C
--   -}
--   ImplL
--     :: DerTerm l a -- D
--     -> DerTerm l a -- D'
--     -> Label l a
--     -> SFormula a
--     -> l -- s
--     -> DerTerm l a
