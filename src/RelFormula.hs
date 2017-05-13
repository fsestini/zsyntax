{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fno-max-relevant-binds #-}

module RelFormula where

import LinearContext
import UnrestrContext
import ForwardSequent
import Data.Foldable
import Prover
import qualified TypeClasses as T

--------------------------------------------------------------------------------
-- Implicational formulas

data ImplKind = IAxiom | IRegular
data BaseSpot :: (* -> *) -> ImplKind -> * -> * where
  EmptySpot :: BaseSpot eb IAxiom a
  FullSpot :: eb a -> BaseSpot eb IRegular a

deriving instance Eq (eb a) => Eq (BaseSpot eb k a)
deriving instance Ord (eb a) => Ord (BaseSpot eb k a)
deriving instance (Show (eb a), Show a) => Show (BaseSpot eb k a)

bsMapAtoms
  :: (T.CanMap eb, T.Constr eb a1, T.Constr eb a2)
  => (a1 -> a2) -> BaseSpot eb k a1 -> BaseSpot eb k a2
bsMapAtoms f EmptySpot = EmptySpot
bsMapAtoms f (FullSpot eb) = FullSpot (T.map f eb)

data ImplFormula :: (* -> *) -> (* -> *) -> ImplKind -> * -> * -> * where
  ImplF
    :: LFormula eb cs k1 a l
    -> BaseSpot eb ik a
    -> cs a
    -> LFormula eb cs k2 a l
    -> l
    -> ImplFormula eb cs ik a l

deriving instance Functor (ImplFormula eb cs k a)
deriving instance Foldable (ImplFormula eb cs k a)
deriving instance Traversable (ImplFormula eb cs k a)
deriving instance
         (Show (eb a), Show (cs a), Show a, Show l) =>
         Show (ImplFormula eb cs k a l)

instance Eq l => Eq (ImplFormula eb cs ik a l) where
  (ImplF _ _ _ _ lbl1) == (ImplF _ _ _ _ lbl2) = lbl1 == lbl2

instance Ord l => Ord (ImplFormula eb cs ik a l) where
  compare (ImplF _ _ _ _ lbl1) (ImplF _ _ _ _ lbl2) = compare lbl1 lbl2

implMapAtoms
  :: ( T.CanMap eb
     , T.Constr eb a1
     , T.Constr eb a2
     , T.CanMap cs
     , T.Constr cs a1
     , T.Constr cs a2
     )
  => (a1 -> a2) -> ImplFormula eb cs k a1 l -> ImplFormula eb cs k a2 l
implMapAtoms f (ImplF f1 spot cs f2 l) =
  ImplF
    (frmlMapAtoms f f1)
    (bsMapAtoms f spot)
    (T.map f cs)
    (frmlMapAtoms f f2)
    l

mapEbBS :: (eb1 a -> eb2 a) -> BaseSpot eb1 k a -> BaseSpot eb2 k a
mapEbBS f EmptySpot = EmptySpot
mapEbBS f (FullSpot eb) = FullSpot (f eb)

mapEbCsI :: (eb1 a -> eb2 a)
         -> (cs1 a -> cs2 a)
         -> ImplFormula eb1 cs1 k a l
         -> ImplFormula eb2 cs2 k a l
mapEbCsI f g (ImplF a bs cs b l) =
  ImplF (mapEbCsF f g a) (mapEbBS f bs) (g cs) (mapEbCsF f g b) l

axiomIsRegular
  :: ElemBase eb a
  => Axiom eb cs a l -> ImplFormula eb cs IRegular a l
axiomIsRegular (ImplF a _ cs b l) = ImplF a (FullSpot mempty) cs b l

axiomIsFormula
  :: ElemBase eb a
  => Axiom eb cs a l -> LFormula eb cs KImpl a l
axiomIsFormula (ImplF a EmptySpot cs b l) = Impl a mempty cs b l



type Axiom eb cs a l = ImplFormula eb cs IAxiom a l

--------------------------------------------------------------------------------
-- Generic labelled formulas

data FKind = KAtom | KConj | KImpl

{-| The type of biological (and non-logical) formulas, which constitute
    the logical atoms.
    It is parameterized over the type of biological atoms. -}
data BioFormula a  =  BioAtom a
                   |  BioInter (BioFormula a) (BioFormula a)
                   deriving (Eq, Ord, Functor, Foldable)

instance Show a => Show (BioFormula a) where
  show (BioAtom x) = show x
  show (BioInter x y) = show x ++ "<>" ++ show y

data LFormula :: (* -> *) -> (* -> *) -> FKind -> * -> * -> * where
  Atom :: BioFormula a -> LFormula eb cs KAtom a l
  Conj
    :: LFormula eb cs k1 a l
    -> LFormula eb cs k2 a l
    -> l
    -> LFormula eb cs KConj a l
  Impl'
    :: ImplFormula eb cs IRegular a l
    -> LFormula eb cs KImpl a l

pattern Impl a eb cs b l = Impl' (ImplF a (FullSpot eb) cs b l)

deriving instance Functor (LFormula eb cs k a)
deriving instance Foldable (LFormula eb cs k a)
deriving instance Traversable (LFormula eb cs k a)

instance (Show a, Show l) => Show (LFormula eb cs k a l) where
  show f = show (label f)

frmlMapAtoms
  :: ( T.CanMap eb
     , T.Constr eb a1
     , T.Constr eb a2
     , T.CanMap cs
     , T.Constr cs a1
     , T.Constr cs a2
     )
  => (a1 -> a2) -> LFormula eb cs k a1 l -> LFormula eb cs k a2 l
frmlMapAtoms f (Atom b) = Atom (fmap f b)
frmlMapAtoms f (Conj f1 f2 l) = Conj (frmlMapAtoms f f1) (frmlMapAtoms f f2) l
frmlMapAtoms f (Impl' i) = Impl' (implMapAtoms f i)

mapEbCsF
  :: (eb1 a -> eb2 a)
  -> (cs1 a -> cs2 a)
  -> LFormula eb1 cs1 k a l
  -> LFormula eb2 cs2 k a l
mapEbCsF f g (Atom a) = Atom a
mapEbCsF f g (Conj f1 f2 l) = Conj (mapEbCsF f g f1) (mapEbCsF f g f2) l
mapEbCsF f g (Impl' i) = Impl' (mapEbCsI f g i)

--------------------------------------------------------------------------------

-- | Opaque formulas
data OLFormula eb cs a l = forall k . OLF (LFormula eb cs k a l)

deriving instance Functor (OLFormula eb cs a)
deriving instance Foldable (OLFormula eb cs a)
deriving instance Traversable (OLFormula eb cs a)

instance (Eq a, Eq l) => Eq (OLFormula eb cs a l) where
  (OLF f1) == (OLF f2) = (label f1) == (label f2)

instance (Ord a, Ord l) => Ord (OLFormula eb cs a l) where
  compare (OLF f1) (OLF f2) = compare (label f1) (label f2)

instance (Show l, Show a) => Show (OLFormula eb cs a l) where
  show (OLF f) = show f

olfMapAtoms
  :: ( T.CanMap eb
     , T.Constr eb a1
     , T.Constr eb a2
     , T.CanMap cs
     , T.Constr cs a1
     , T.Constr cs a2
     )
  => (a1 -> a2) -> OLFormula eb cs a1 l -> OLFormula eb cs a2 l
olfMapAtoms f (OLF frml) = OLF (frmlMapAtoms f frml)

--------------------------------------------------------------------------------
-- Eq, Ord instances for formulas

data Label a l = L l | A (BioFormula a) deriving (Eq, Ord, Show)

label :: LFormula eb cs k a l -> Label a l
label (Atom a) = A a
label (Conj _ _ lbl) = L lbl
label (Impl _ _ _ _ lbl) = L lbl

instance (Eq a, Eq l) => Eq (LFormula eb cs k a l) where
  f1 == f2 = (label f1) == (label f2)

instance (Ord a, Ord l) => Ord (LFormula eb cs k a l) where
  compare f1 f2 = compare (label f1) (label f2)

--------------------------------------------------------------------------------
-- Elementary bases and control sets

class (ControlSet cs a, ElemBase eb a) => BaseCtrl eb cs a where
  respects :: eb a -> cs a -> Bool

class (Monoid (cs a), Eq (cs a)) =>
      ControlSet cs a

-- | Typeclass of elementary bases
class (Monoid (eb a), Eq (eb a)) =>
      ElemBase eb a where
  singleton :: BioFormula a -> eb a

elemBase
  :: ElemBase eb a
  => NeutralFormula eb cs a l -> eb a
elemBase (NF (Atom a)) = singleton a
-- elemBase (NF (Conj f1 f2 _)) = elemBase (NF f1) `mappend` elemBase (NF f2)
elemBase (NF (Impl _ eb _ _ _)) = eb

elemBaseAll
  :: (ElemBase eb a, Foldable f)
  => f (NeutralFormula eb cs a l) -> eb a
elemBaseAll = fold . map elemBase . toList

--------------------------------------------------------------------------------
-- Neutral formulas and sequents

class IsNeutral (k :: FKind) where
  decideNeutral
    :: LFormula eb cs k a l
    -> Either (LFormula eb cs KAtom a l) (LFormula eb cs KImpl a l)

instance IsNeutral KAtom where
  decideNeutral = Left

instance IsNeutral KImpl where
  decideNeutral = Right

data NeutralFormula eb cs a l =
  forall (k :: FKind) . IsNeutral k =>
            NF (LFormula eb cs k a l)

nfMapAtoms
  :: ( T.CanMap eb
     , T.Constr eb a1
     , T.Constr eb a2
     , T.CanMap cs
     , T.Constr cs a1
     , T.Constr cs a2
     )
  => (a1 -> a2) -> NeutralFormula eb cs a1 l -> NeutralFormula eb cs a2 l
nfMapAtoms f (NF frml) = NF (frmlMapAtoms f frml)

instance (Eq a, Eq l) => Eq (NeutralFormula eb cs a l) where
  (NF f1) == (NF f2) = (label f1) == (label f2)

instance (Ord a, Ord l) => Ord (NeutralFormula eb cs a l) where
  compare (NF f1) (NF f2) = compare (label f1) (label f2)

deriving instance Functor (NeutralFormula eb cs a)
deriving instance Foldable (NeutralFormula eb cs a)
deriving instance Traversable (NeutralFormula eb cs a)

instance (Show a, Show l) => Show (NeutralFormula eb cs a l) where
  show (NF f) = show f

type UCtxt eb cs a l = UnrestrCtxt (Axiom eb cs a l)
type LCtxt eb cs a l = LinearCtxt (NeutralFormula eb cs a l)

data NeutralSequent eb cs a l =
  NS (UCtxt eb cs a l)
     (LCtxt eb cs a l)
     (cs a)
     (OLFormula eb cs a l)
  deriving (Eq, Ord)

instance (Show (eb a), Show (cs a), Show a, Show l) =>
         Show (NeutralSequent eb cs a l) where
  show (NS uc lc cs concl) =
    show uc ++ " ; " ++ show lc ++ " ==> " ++ show concl

data GoalNeutralSequent eb cs a l =
  GNS (UCtxt eb cs a l)
      (LCtxt eb cs a l)
      (Maybe (cs a))
      (OLFormula eb cs a l)
  deriving (Eq, Ord, Show)

instance (Ord l, Ord a, Eq (cs a)) =>
         ForwardSequent (NeutralSequent eb cs a l) where
  (NS un1 lin1 cs1 concl1) `subsumes` (NS un2 lin2 cs2 concl2) =
    un1 <= un2 && lin1 == lin2 && cs1 == cs2 && concl1 == concl2

instance (Ord l, Ord a, Eq (cs a)) =>
         SearchPair (NeutralSequent eb cs a l) (GoalNeutralSequent eb cs a l) where
  isSubsequent _ _ = True
  subsumesGoal ns@(NS _ _ cs1 _) (GNS un2 lin2 hole concl2) = ns `subsumes` gseq
    where
      gseq = NS un2 lin2 gcs concl2
      gcs =
        case hole of
          Nothing -> cs1
          Just cs -> cs

gnsMapAtoms
  :: ( T.CanMap eb
     , T.Constr eb a1
     , T.Constr eb a2
     , T.CanMap cs
     , T.Constr cs a1
     , T.Constr cs a2
     , Ord l
     , Ord a1
     , Ord a2
     )
  => (a1 -> a2) -> GoalNeutralSequent eb cs a1 l -> GoalNeutralSequent eb cs a2 l
gnsMapAtoms f (GNS uc lc cs concl) =
  GNS
    (T.map (implMapAtoms f) uc)
    (T.map (nfMapAtoms f) lc)
    (fmap (T.map f) cs)
    (olfMapAtoms f concl)

--------------------------------------------------------------------------------

-- Deep heterogeneous comparison functions
deepHetCompare
  :: (Ord a, Ord l, Ord (eb a), Ord (cs a))
  => LFormula eb cs k1 a l -> LFormula eb cs k2 a l -> Ordering
deepHetCompare (Atom x1) (Atom x2) = compare x1 x2
deepHetCompare (Atom _) _ = LT
deepHetCompare (Conj a1 b1 lbl1) (Conj a2 b2 lbl2) =
  if ca == EQ
    then if cb == EQ
           then cl
           else cb
    else ca
  where
    ca = deepHetCompare a1 a2
    cb = deepHetCompare b1 b2
    cl = compare lbl1 lbl2
deepHetCompare (Conj _ _ _) (Atom _) = GT
deepHetCompare (Conj _ _ _) (Impl' _) = LT
deepHetCompare (Impl' i1) (Impl' i2) = deepImplCompare i1 i2
deepHetCompare (Impl' _) _ = GT

deepSpotCompare
  :: Ord (eb a)
  => BaseSpot eb k1 a -> BaseSpot eb k2 a -> Ordering
deepSpotCompare EmptySpot EmptySpot = EQ
deepSpotCompare EmptySpot _ = LT
deepSpotCompare (FullSpot eb1) (FullSpot eb2) = compare eb1 eb2
deepSpotCompare (FullSpot _) EmptySpot = GT

deepImplCompare
  :: (Ord a, Ord l, Ord (eb a), Ord (cs a))
  => ImplFormula eb cs k1 a l -> ImplFormula eb cs k2 a l -> Ordering
deepImplCompare (ImplF a1 spot1 cs1 b1 l1) (ImplF a2 spot2 cs2 b2 l2) =
  if ca == EQ
    then if cb == EQ
           then if ceb == EQ
                  then if ccs == EQ
                         then cl
                         else ccs
                  else ceb
           else cb
    else ca
  where
    ca = deepHetCompare a1 a2
    cb = deepHetCompare b1 b2
    ceb = deepSpotCompare spot1 spot2
    ccs = compare cs1 cs2
    cl = compare l1 l2

--------------------------------------------------------------------------------
-- Show instances

deepShowAtom :: Show a => BioFormula a -> String
deepShowAtom (BioAtom a) = show a
deepShowAtom (BioInter a1 a2) = deepShowAtom a1 ++ "<>" ++ deepShowAtom a2

deepShowFormula :: Show a => LFormula eb cs k a l -> String
deepShowFormula (Atom a) = deepShowAtom a
deepShowFormula (Conj f1 f2 _) = deepShowFormula f1 ++ " * " ++ deepShowFormula f2
deepShowFormula (Impl' i) = deepShowImpl i

deepShowImpl (ImplF f1 _ _ f2 _) =
  deepShowFormula f1 ++ " -> " ++ deepShowFormula f2
