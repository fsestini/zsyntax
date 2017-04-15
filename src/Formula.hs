{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds, KindSignatures, GADTs #-}

{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Formula where

import qualified Data.Map.Strict as M
import qualified Data.Set as S

data BioFormula a  =  BioAtom a
                   |  BioInter (BioFormula a) (BioFormula a)
                   deriving(Eq, Ord, Show)

data Bias = LeftBias | RightBias
data Pole  =  LSRA -- Left synch, right asynch
           |  LARS -- Left asynch, right synch
           |  AtomPole

data Atom :: Bias -> * -> * where
  LBAtom  ::  BioFormula a  ->  Atom LeftBias a
  RBAtom  ::  BioFormula a  ->  Atom RightBias a

-- | Type of labelled formulae.
--   An atom does not have a label, since it is its own label.
data LFormula :: Pole -> * -> * -> * where
  FAtom :: Atom b a -> LFormula AtomPole l a
  FConj :: LFormula p l a -> LFormula q l a -> l -> LFormula LARS l a
  FImpl :: LFormula p l a -> LFormula q l a -> l -> LFormula LSRA l a

class IsRightSynchronous (p :: Pole) where

instance IsRightSynchronous LARS where
instance IsRightSynchronous AtomPole where

class IsLeftSynchronous (p :: Pole) where

instance IsLeftSynchronous LSRA where
instance IsLeftSynchronous AtomPole where

data Label l a = L l | A (BioFormula a) deriving (Eq)

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
