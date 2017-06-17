{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds, KindSignatures, GADTs #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

{-| Formulae of Zsyntax. -}
module Formula where

import qualified Data.Set as S

{-| The type of biological (and non-logical) formulas, which constitute
    the logical atoms.
    It is parameterized over the type of biological atoms. -}
data BioFormula a  =  BioAtom a
                   |  BioInter (BioFormula a) (BioFormula a)
                   deriving (Eq, Ord, Show)

-- | Type of biases of logical atoms in the focused calculus.
data Bias = LeftBias | RightBias

{-| Type of possible polarizations of formulas of the focused calculus.
    Non-atomic formulas can either be left-synchronous (or, equivalently,
    right-asynchronous), or left-asynchronous (or, equivalently,
    right-synchronous). Atoms can be both left- or right- synchronous, hence
    have a dedicated pole. -}
data Pole  =  LSRA
           |  LARS
           |  AtomPole

{-| Type of logical atoms, which are biological formulas with a bias. -}
data Atom :: Bias -> * -> * where
  LBAtom  ::  BioFormula a  ->  Atom LeftBias a
  RBAtom  ::  BioFormula a  ->  Atom RightBias a

{-| Type of labelled formulas.
    It is parameterized by the pole of the formula, which depends on the
    constructor used, and type of labels and the type of biological atoms.
    An atom does not have an explicit label, since it is its own label. -}
data LFormula :: Pole -> * -> * -> * where
  FAtom :: Atom b a -> LFormula AtomPole l a
  FConj :: LFormula p l a -> LFormula q l a -> l -> LFormula LARS l a
  FImpl
    :: LFormula p l a
    -> LFormula q l a
    -> l
    -> LFormula LSRA l a

-- | Class of right-synchronous poles, used as a predicate over poles.
class IsRightSynchronous (p :: Pole) where
  decideRS :: LFormula p l a -> Either (OAtom a) (LFormula LARS l a)

-- | A formula which is left-asynchronous/right-synchronous is indeed
-- right-synchronous.
instance IsRightSynchronous LARS where
  decideRS = Right

-- | A formula with atomic pole is an atom, hence both a left- and right-
-- synchronous formula by definition.
instance IsRightSynchronous AtomPole where
  decideRS (FAtom a) = Left (OA a)

-- | Class of left-synchronous poles, used as a predicate over poles.
class IsLeftSynchronous (p :: Pole) where
  decideLS :: LFormula p l a -> Either (OAtom a) (LFormula LSRA l a)

-- | A formula which is left-synchronous/right-asynchronous is indeed
-- left-synchronous.
instance IsLeftSynchronous LSRA where
  decideLS = Right

-- | A formula with atomic pole is an atom, hence both a left- and right-
-- synchronous formula by definition.
instance IsLeftSynchronous AtomPole where
  decideLS (FAtom a) = Left (OA a)

{-| Type of labels, which can either be pure labels of atomic formulas. -}
data Label l a = L l | A (BioFormula a) deriving (Eq, Ord, Show)

-- | Returns the label of a given labelled formula.
label :: LFormula p l a -> Label l a
label (FAtom (LBAtom bf)) = A bf
label (FAtom (RBAtom bf)) = A bf
label (FConj _ _ l) = L l
label (FImpl _ _ l) = L l

--------------------------------------------------------------------------------
-- Opaque formulas

-- | Type of opaque formulas.
data OLFormula l a = forall p . OLF (LFormula p l a)

instance (Ord a, Ord l) => Eq (OLFormula l a) where
  (OLF f1) == (OLF f2) = compareLF f1 f2 == EQ

instance (Ord a, Ord l) => Ord (OLFormula l a) where
  compare (OLF f1) (OLF f2) = compareLF f1 f2

compareLF :: (Ord a, Ord l) => LFormula p l a -> LFormula q l a -> Ordering
compareLF (FAtom atom1) (FAtom atom2) =
  compare (OA atom1) (OA atom2)
compareLF (FConj f1 f2 l1) (FConj g1 g2 l2) =
  case compareLF f1 g1 of
    EQ ->
      case compareLF f2 g2 of
        EQ -> compare l1 l2
        x -> x
    x -> x
compareLF (FImpl f1 f2 l1) (FImpl g1 g2 l2) =
  case compareLF f1 g1 of
    EQ ->
      case compareLF f2 g2 of
        EQ -> compare l1 l2
        x -> x
    x -> x
compareLF (FAtom _) _ = LT
compareLF (FConj _ _ _) (FAtom _) = GT
compareLF (FConj _ _ _) (FImpl _ _ _) = LT
compareLF (FImpl _ _ _) _ = GT

-- | Type of opaque left-synchronous labelled formulas.
data OLSLFormula l a =
  forall p. (IsLeftSynchronous p) =>
            OLSLF (LFormula p l a)

-- | Type of opaque right-synchronous labelled formulas.
data ORSLFormula l a =
  forall p. (IsRightSynchronous p) =>
            ORSLF (LFormula p l a)

data OAtom a = forall b . OA (Atom b a)

instance Ord a => Eq (OAtom a) where
  (OA a1) == (OA a2) = compareAtom a1 a2 == EQ

instance Ord a => Ord (OAtom a) where
  compare (OA a1) (OA a2) = compareAtom a1 a2

compareAtom :: Ord a => Atom b1 a -> Atom b2 a -> Ordering
compareAtom atom1 atom2 = compare (getAtom atom1) (getAtom atom2)
  where
    getAtom :: Atom b a -> BioFormula a
    getAtom (LBAtom atom) = atom
    getAtom (RBAtom atom) = atom


olfLabel :: OLFormula l a -> Label l a
olfLabel (OLF f) = label f

olsfLabel :: OLSLFormula l a -> Label l a
olsfLabel (OLSLF f) = label f

--------------------------------------------------------------------------------
-- Neutral sequents.
--
-- Although the search procedure uses labelled sequents, here we give the type
-- of fully specified sequents.

data NeutralSequent l a where
  NSQ
    :: (IsRightSynchronous p)
    => S.Set (OLFormula l a)
    -> [OLSLFormula l a]
    -> LFormula p l a
    -> NeutralSequent l a
