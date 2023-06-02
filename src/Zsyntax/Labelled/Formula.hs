{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Zsyntax.Labelled.Formula
  (
   Label
  -- FKind(..)
  , ElemBase(..)
  , ReactionList
  -- * Labelled formulas
  , LFormula(..)
  , LAtom(..)
  , LConj(..)
  , LImpl(..)
  , pattern Atom
  , pattern Conj
  , pattern Impl
  , foldLSum
  , injAtom
  , injConj
  , injImpl
  , ppLFormula
  , elemBase
  , label
  -- , frmlHetEq
  -- , frmlHetOrd
  , deepHetComp
  -- * Labelled axioms
  , LAxiom(..)
  , axLabel
  , axToFormula
  , ppLAxiom
  , traverseAtoms
  , traverseAtom
  , traverseConj
  , traverseImpl
  , traverseAxiom
  , traverseElemBase
  , traverseRL
  -- -- * Opaque formulas
  -- , Opaque(..)
  -- , withOpaque
  -- , oConj
  -- , oImpl
  -- * Basic formulas
  , BFormula(..)
  , bAtom
  , bConj
  , bfToFormula
  , bfToAtoms
  , maybeBFormula
  ) where

import Zsyntax.ReactionList
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as M
import Data.Foldable (fold)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Bifunctor.Sum (Sum (..))
import Data.Function (on)
import Data.Bitraversable (Bitraversable(bitraverse))
import Data.Text (Text)

newtype ElemBase a = ElemBase { unEB :: MultiSet a }
  deriving (Semigroup, Monoid, Eq, Ord, Show)

traverseElemBase :: (Ord b, Applicative f) => (a -> f b) -> ElemBase a -> f (ElemBase b)
traverseElemBase f (ElemBase b) =
  ElemBase . M.fromList <$> traverse f (M.toList b)

-- data FKind = KAtom | KConj | KImpl

type ReactionList a = RList (ElemBase a) (CtrlSet a)

traverseRL :: (Applicative f, Ord b) => (a -> f b) -> ReactionList a -> f (ReactionList b)
traverseRL f = bitraverse (traverseElemBase f) (traverseCtrlSet f)

newtype LAtom a l = LAtom { atomAtom :: a }
  deriving (Show, Functor, Foldable, Traversable)
data LConj a l = LConj
  { conjLhs  :: LFormula a l
  , conjRhs :: LFormula a l
  , conjLabel :: l
  } deriving (Show, Functor, Foldable, Traversable)
data LImpl a l = LImpl
  { implLhs  :: LFormula a l
  , implBase :: ElemBase a
  , implRL   :: ReactionList a
  , implRhs  :: LFormula a l
  , implLabel :: l
  } deriving (Show, Functor, Foldable, Traversable)

instance Eq a => Eq (LAtom a l) where (==) = on (==) atomAtom
instance Eq l => Eq (LImpl a l) where (==) = on (==) implLabel
instance Eq l => Eq (LConj a l) where (==) = on (==) conjLabel

instance Ord a => Ord (LAtom a l) where compare = on compare atomAtom
instance Ord l => Ord (LConj a l) where compare = on compare conjLabel
instance Ord l => Ord (LImpl a l) where compare = on compare implLabel

-- | Type of labelled formulas, parameterized by the type of the labels and of
-- the logical atoms.
newtype LFormula a l = LFormula { unLFormula :: Sum LAtom (Sum LConj LImpl) a l }
  deriving newtype (Show, Functor, Foldable)

instance Traversable (LFormula a) where
  traverse f (LFormula x) = LFormula <$> traverse f x

pattern Atom x = LFormula (L2 (LAtom x))
pattern Conj x y l = LFormula (R2 (L2 (LConj x y l)))
pattern Impl x b r y l = LFormula (R2 (R2 (LImpl x b r y l)))
{-# COMPLETE Atom, Conj, Impl #-}

foldLSum :: (LAtom a l -> b) -> (LConj a l -> b) -> (LImpl a l -> b)
         -> LFormula a l -> b
foldLSum f g h (LFormula x) = case x of
  L2 a -> f a
  R2 (L2 c) -> g c
  R2 (R2 i) -> h i

injAtom :: LAtom a l -> LFormula a l
injAtom = LFormula . L2

injConj :: LConj a l -> LFormula a l
injConj = LFormula . R2 . L2

injImpl :: LImpl a l -> LFormula a l
injImpl = LFormula . R2 . R2

type Label a l = Either a l

-- | Returns the label of a labelled formula.
label :: LFormula a l -> Label a l
label = \case
  Atom a -> Left a
  Conj _ _ l -> Right l
  Impl _ _ _ _ l -> Right l

-- | Perform an effectful traversal of all atomic subformulas.
--
-- `LFormula` is not functorial in the first index, hence not even bitraversable,
-- so this needs a dedicated function, for which no laws can be guaranteed.
traverseAtoms :: (Ord b, Applicative f) => (a -> f b) -> LFormula a l -> f (LFormula b l)
traverseAtoms f (LFormula x) = LFormula <$> case x of
  L2 a -> L2 <$> traverseAtom f a
  R2 (L2 c) -> R2 . L2 <$> traverseConj f c
  R2 (R2 i) -> R2 . R2 <$> traverseImpl f i

traverseAtom :: Functor f => (a -> f b) -> LAtom a l -> f (LAtom b l)
traverseAtom f (LAtom x) = LAtom <$> f x

traverseConj :: (Ord b, Applicative f) => (a -> f b) -> LConj a l -> f (LConj b l)
traverseConj f (LConj a b l) =
  LConj <$> traverseAtoms f a <*> traverseAtoms f b <*> pure l

traverseImpl :: (Ord b, Applicative f) => (a -> f b) -> LImpl a l -> f (LImpl b l)
traverseImpl f (LImpl x b r y l) =
  LImpl <$> traverseAtoms f x
        <*> traverseElemBase f b
        <*> bitraverse (traverseElemBase f) (traverseCtrlSet f) r
        <*> traverseAtoms f y <*> pure l


{-

data LFormula :: FKind -> Type -> Type -> Type where
  Atom :: a -> LFormula KAtom a l
  Conj
    :: LFormula k1 a l
    -> LFormula k2 a l
    -> l
    -> LFormula KConj a l
  Impl
    :: LFormula k1 a l
    -> ElemBase a
    -> ReactionList a
    -> LFormula k2 a l
    -> l
    -> LFormula KImpl a l

deriving instance (Show a, Show l) => Show (LFormula k a l)

-- | Heterogeneous equality test between labelled formulas.
--
-- This function just compares the formulas' labels for equality, under the
-- assumption that labels have been assigned in a sensible way.
frmlHetEq :: (Eq a, Eq l) => LFormula k1 a l -> LFormula k2 a l -> Bool
frmlHetEq f1 f2 = label f1 == label f2

-- | Heterogeneous comparison between labelled formulas.
--
-- This function just compares the formulas' labels, under the assumption that
-- labels have been assigned in a sensible way.
frmlHetOrd :: (Ord a, Ord l) => LFormula k1 a l -> LFormula k2 a l -> Ordering
frmlHetOrd f1 f2 = compare (label f1) (label f2)
-}

instance (Eq a, Eq l) => Eq (LFormula a l) where
  (==) = on (==) label

foldF
  :: (a -> b)
  -> (b -> b -> l -> b)
  -> (b -> ElemBase a -> ReactionList a -> b -> l -> b)
  -> LFormula a l -> b
foldF f _ _ (Atom a) = f a
foldF f g h (Conj f1 f2 l) = g (foldF f g h f1) (foldF f g h f2) l
foldF f g h (Impl f1 eb cty f2 l) = h (foldF f g h f1) eb cty (foldF f g h f2) l

-- | Pretty-print labelled implications.
ppLImpl :: (a -> Text) -> LImpl a l -> Text
ppLImpl p (LImpl a _ _ b _) =
  fold ["(", ppLFormula p a, " → ", ppLFormula p b, ")"]

-- | Pretty-print labelled formulas, given a way to pretty-print its atoms.
--
-- Note that this function ignores labels, for which one should use the 'Show'
-- instance.
ppLFormula :: (a -> Text) -> LFormula a l -> Text
ppLFormula p = foldF p (\a b _ -> fold [a, " ⊗ ", b])
                     (\a _ _ b _ -> fold ["(", a, " → ", b, ")"])

-- | Returns the elementary base of a labelled formula.
elemBase :: Ord a => LFormula a l -> ElemBase a
elemBase = foldF (ElemBase . M.singleton) (\a b _ -> a <> b) (\_ e _ _ _ -> e)

{-

--------------------------------------------------------------------------------
-- Opaque formulas

-- | Type of opaque formulas, that is, those for which we do not care about
-- their formula kind.
data Opaque a l = forall k . O (LFormula k a l)

deriving instance (Show a, Show l) => Show (Opaque a l)

instance (Eq l, Eq a) => Eq (Opaque a l) where
  O f1 == O f2 = frmlHetEq f1 f2

instance (Ord l, Ord a) => Ord (Opaque a l) where
  compare (O f1) (O f2) = frmlHetOrd f1 f2

withOpaque :: (forall k . LFormula k a l -> b) -> Opaque a l -> b
withOpaque f (O fr) = f fr

-- | Constructs the conjunction of two opaque formulas. The result is a provably
-- conjunctive labelled formula.
oConj :: Opaque a l -> Opaque a l -> l -> LFormula KConj a l
oConj (O f1) (O f2) = Conj f1 f2

-- | Constructs the Zsyntax conditional (aka linear implication) between two
-- opaque formulas, whose reaction is described by a given elementary base and
-- reaction list. The result is a provably implicational labelled formula.
oImpl :: Opaque a l -> ElemBase a -> ReactionList a -> Opaque a l -> l
      -> LFormula KImpl a l
oImpl (O f1) eb cty (O f2) = Impl f1 eb cty f2

-}

--------------------------------------------------------------------------------
-- Basic formulas

-- | Type of basic formulas.
-- A basic formula is one composed of conjunctions of atoms.
data BFormula a l = BAtom a | BConj (BFormula a l) (BFormula a l) l
  deriving (Functor, Foldable, Traversable, Show)

traverseBFormula :: Applicative f => (a -> f b) -> BFormula a l -> f (BFormula b l)
traverseBFormula f = \case
  BAtom a -> BAtom <$> f a
  BConj x y l -> BConj <$> traverseBFormula f x <*> traverseBFormula f y <*> pure l

-- | Constructs a basic formula from a logical atom.
bAtom :: a -> BFormula a l
bAtom = BAtom

-- | Constructs the conjunction of two basic formulas, with a given label.
bConj :: l -> BFormula a l -> BFormula a l -> BFormula a l
bConj l f1 f2 = BConj f1 f2 l

-- data ExBFormula a l = forall k . ExBFormula (LFormula k a l)

-- | Returns the labelled formula corresponding to a given basic formula.
--
-- Note that the result formula is opaque, since it could be an atom as well as
-- a conjunction, and thus has no determined index.
bfToFormula :: BFormula a l -> LFormula a l
bfToFormula (BAtom x) = Atom x
bfToFormula (BConj f1 f2 l) = Conj (bfToFormula f1) (bfToFormula f2) l

-- | Unrolls a basic formula, discarding all labels and returning a (non-empty)
-- list of all its constituent logical atoms.
bfToAtoms :: BFormula a l -> NonEmpty a
bfToAtoms (BAtom bf) = bf :| []
bfToAtoms (BConj f1 f2 _) = bfToAtoms f1 <> bfToAtoms f2

-- | Decides whether the input labelled formula is a basic formula, and if so,
-- it returns it wrapped in 'Just' as a proper basic formula.
maybeBFormula :: LFormula a l -> Maybe (BFormula a l)
maybeBFormula (Atom x) = pure (BAtom x)
maybeBFormula (Conj f1 f2 l) =
  BConj <$> maybeBFormula f1 <*> maybeBFormula f2 <*> pure l
maybeBFormula Impl {} = Nothing
-- was: decideF

--------------------------------------------------------------------------------

data LAxiom a l = LAx (BFormula a l) (ReactionList a) (BFormula a l) l
  deriving (Show, Functor, Foldable, Traversable)

traverseAxiom :: (Applicative f, Ord b) => (a -> f b) -> LAxiom a l -> f (LAxiom b l)
traverseAxiom f (LAx x r y l) =
  LAx <$> traverseBFormula f x
      <*> bitraverse (traverseElemBase f) (traverseCtrlSet f) r
      <*> traverseBFormula f y
      <*> pure l

-- | Converts a labelled axiom to a labelled formula.
axToFormula :: Ord a => LAxiom a l -> LImpl a l
axToFormula (LAx f1 _ f2 l) = LImpl f1' mempty mempty f2' l
  where f1' = bfToFormula f1 ; f2' =  bfToFormula f2
  -- case (bfToFormula f1, bfToFormula f2) of
  -- (O f1', O f2') ->
  --   Impl (mapCty (const mempty) f1') mempty mempty (mapCty (const mempty) f2') l

-- | Pretty-prints a labelled axiom, given a way to pretty-print its atoms.
--
-- Note that this function ignores labels, for which one should rely on the
-- 'Show' instance.
ppLAxiom :: Ord a => (a -> Text) -> LAxiom a l -> Text
ppLAxiom p ax = ppLImpl p (axToFormula ax)

-- -- | Type of formula labels. Note that logical atoms are their own labels.
-- data Label a l
--   = L l -- ^ Regular label
--   | A a -- ^ Logical atom
--   deriving (Eq, Ord, Show)

-- | Returns the label of a labelled axiom.
axLabel :: LAxiom a l -> l
axLabel (LAx _ _ _ l) = l

{-
--------------------------------------------------------------------------------
-- Mapping functions

-- mapAtoms :: Ord a' => (a -> a') -> LFormula k a l -> LFormula k a' l
-- mapAtoms f (Atom a) = Atom (f a)
-- mapAtoms f (Conj a b l) = Conj (mapAtoms f a) (mapAtoms f b) l
-- mapAtoms f (Impl a e c b l) =
--   Impl (mapAtoms f a) (over pack (MS.map f) e) c (mapAtoms f b) l

mapCty :: (ReactionList a -> ReactionList a) -> LFormula k a l -> LFormula k a l
mapCty _ (Atom a) = Atom a
mapCty f (Conj f1 f2 l) = Conj (mapCty f f1) (mapCty f f2) l
mapCty f (Impl f1 eb cty f2 l) = Impl (mapCty f f1) eb (f cty) (mapCty f f2) l

-- mapCtyAx :: (cty1 -> cty2) -> LAxiom a l -> LAxiom a l
-- mapCtyAx f (LAx f1 cty f2 l) = LAx f1 (f cty) f2 l

-}

--------------------------------------------------------------------------------
-- Deep heterogeneous comparison functions

isEq :: Ordering -> Either Ordering Ordering
isEq x = if x == EQ then Right x else Left x

-- | Returns the result of a deep heterogeneous comparison between two labelled formulas.
--
-- Comparison is "deep" in the sense that is considers the entire recursive
-- structure of formulas. This is unlike 'frmlHetOrd', which only compares
-- labels.
deepHetComp :: (Ord a, Ord l) => LFormula a l -> LFormula a l -> Ordering
deepHetComp (Atom x1) (Atom x2) = compare x1 x2
deepHetComp (Atom _) _ = LT
deepHetComp (Conj a1 b1 l1) (Conj a2 b2 l2) =
  either id id $ isEq ca >> isEq cb >> pure cl
  where ca = deepHetComp a1 a2 ; cb = deepHetComp b1 b2 ; cl = compare l1 l2
deepHetComp Conj{} (Atom _) = GT
deepHetComp Conj{} Impl{} = LT
deepHetComp (Impl a1 eb1 cs1 b1 l1) (Impl a2 eb2 cs2 b2 l2) =
  either id id $ isEq ca >> isEq cb >> isEq ceb >> isEq ccs >> pure cl
  where
    ca = deepHetComp a1 a2 ; cb = deepHetComp b1 b2 ; ceb = compare eb1 eb2
    ccs = compare cs1 cs2 ; cl = compare l1 l2
deepHetComp Impl{} _ = GT


--------------------------------------------------------------------------------

-- -- | Type of labelled formulas to be used during proof search.
-- newtype SrchFormula a l k = Srch { unSrch :: LFormula k a l }

-- instance (Show a, Show l) => Show1 (SrchFormula a l) where
--   show1 (Srch f) = show f

-- instance (Ord a, Ord l) => HEq (SrchFormula cty a l) where
--   hetCompare (Srch f1) (Srch f2) = compare (label f1) (label f2)

instance Eq l => Eq (LAxiom a l) where
  ax1 == ax2 = axLabel ax1 == axLabel ax2

instance Ord l => Ord (LAxiom a l) where
  compare ax1 ax2 = compare (axLabel ax1) (axLabel ax2)

-- type instance Atom (SrchFormula cty a l) = a
-- type instance Eb (SrchFormula cty a l) = ElemBase a
-- type instance Ax (SrchFormula cty a l) = LAxiom cty a l

-- sfrmlView :: SrchFormula cty a l k
--           -> FrmlView (SrchFormula cty a l) k (ElemBase a) cty a
-- sfrmlView (Srch (Atom a)) = AtomRepr a
-- sfrmlView (Srch (Conj f1 f2 _)) = ConjRepr (Srch f1) (Srch f2)
-- sfrmlView (Srch (Impl f1 e c f2 _)) = ImplRepr (Srch f1) e c (Srch f2)

-- decideN :: Neutral (SrchFormula cty a l) -> Maybe (BFormula a l)
-- decideN = switchN (\(Srch (Atom x)) -> Just (BAtom x)) (const Nothing)

-- decideOF :: Opaque (SrchFormula cty a l) -> Maybe (BFormula a l)
-- decideOF (O (Srch f)) = decideF f
