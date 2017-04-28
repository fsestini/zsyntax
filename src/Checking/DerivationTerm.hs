module Checking.DerivationTerm where

import Formula

data DerTerm l a
  = Init (BioFormula a)
  | Copy (DerTerm l a)
         (Label l a)
  | ConjR (DerTerm l a)
          (DerTerm l a)
          l
  | ConjL (DerTerm l a)
          (Label l a)
          (Label l a)
          l
  | ImplR (DerTerm l a)
          (Label l a)
          l
  | ImplL (DerTerm l a)
          (DerTerm l a)
          (Label l a)
          l
