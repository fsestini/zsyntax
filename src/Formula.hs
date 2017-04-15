{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds, KindSignatures, GADTs #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

{-| Formulae of Zsyntax. -}
module Formula where

import qualified Data.Map.Strict as M
import qualified Data.Set as S

{-| The type of biological (and non-logical) formulas, which constitute
    the logical atoms.
    It is parameterized over the type of biological atoms. -}
data BioFormula a  =  BioAtom a
                   |  BioInter (BioFormula a) (BioFormula a)
                   deriving(Eq, Ord, Show)

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
  FImpl :: LFormula p l a -> LFormula q l a -> l -> LFormula LSRA l a

-- | Class of right-synchronous poles, used as a predicate over poles.
class IsRightSynchronous (p :: Pole) where

-- | A formula which is left-asynchronous/right-synchronous is indeed
-- right-synchronous.
instance IsRightSynchronous LARS where

-- | A formula with atomic pole is an atom, hence both a left- and right-
-- synchronous formula by definition.
instance IsRightSynchronous AtomPole where

-- | Class of left-synchronous poles, used as a predicate over poles.
class IsLeftSynchronous (p :: Pole) where

-- | A formula which is left-synchronous/right-asynchronous is indeed
-- left-synchronous.
instance IsLeftSynchronous LSRA where

-- | A formula with atomic pole is an atom, hence both a left- and right-
-- synchronous formula by definition.
instance IsLeftSynchronous AtomPole where

{-| Type of labels, which can either be pure labels of atomic formulas. -}
data Label l a = L l | A (BioFormula a) deriving (Eq)

-- | Returns the label of a given labelled formula.
label :: LFormula p l a -> Label l a
label (FAtom (LBAtom bf)) = A bf
label (FAtom (RBAtom bf)) = A bf
label (FConj _ _ l) = L l
label (FImpl _ _ l) = L l

type UnrestrCtxt l a = S.Set (Label l a)

emptyUnrestrCtxt = S.empty

data PosNat = One | Succ PosNat deriving(Eq, Show)

toInt :: PosNat -> Int
toInt One       =  1
toInt (Succ n)  =  toInt n + 1

type LinearCtxt l a = M.Map (Label l a) PosNat

emptyLinearCtxt = M.empty

addToLinCtxt :: (Label l a) -> LinearCtxt l a -> LinearCtxt l a
addToLinCtxt = undefined

addToUnrestrCtxt :: (Label l a) -> UnrestrCtxt l a -> UnrestrCtxt l a
addToUnrestrCtxt = undefined

mergeLinearCtxt :: LinearCtxt l a -> LinearCtxt l a -> LinearCtxt l a
mergeLinearCtxt = undefined

mergeUnrestrCtxt :: UnrestrCtxt l a -> UnrestrCtxt l a -> UnrestrCtxt l a
mergeUnrestrCtxt = undefined

singletonLinearCtxt :: Label l a -> LinearCtxt l a
singletonLinearCtxt = undefined

newtype SchemaUCtxt l a = SUC (UnrestrCtxt l a)
newtype SchemaLCtxt l a = SLC (LinearCtxt l a)

matchUnrestrCtxt :: SchemaUCtxt l a -> UnrestrCtxt l a -> Maybe (UnrestrCtxt l a)
matchUnrestrCtxt (SUC suc) uc = undefined

matchLinearCtxt :: SchemaLCtxt l a -> LinearCtxt l a -> Maybe (LinearCtxt l a)
matchLinearCtxt (SLC slc) lc = undefined

data LabelledSequent l a  =  LS (UnrestrCtxt l a) (LinearCtxt l a) (Label l a)

instance Eq (LabelledSequent l a) where
  (==) = undefined

instance Ord (LabelledSequent l a) where
  compare = undefined

--------------------------------------------------------------------------------
-- Decorated formulas

data DecLFormula :: * -> * -> * where
  UnrestrDLF :: LFormula p l a -> DecLFormula l a
  LinearNegativeDLF
    :: (IsLeftSynchronous p)
    => LFormula p l a -> DecLFormula l a
  LinearPositiveDLF
    :: (IsRightSynchronous p)
    => LFormula p l a -> DecLFormula l a
