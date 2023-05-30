{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Zsyntax.ReactionList where

-- import Core.LinearContext
import Data.Set (Set)
import qualified Data.Set as S (map, fromList, toList)
import Data.Bifunctor (first, Bifunctor (..))
import Data.Foldable (toList)
import Data.MultiSet (MultiSet, isSubsetOf)
import qualified Data.MultiSet as M
import Data.Bitraversable (Bitraversable (..))
import Data.Bifoldable (Bifoldable (..))
-- import Data.MultiSet.NonEmpty

traverseSet :: (Applicative f, Ord b) => (a -> f b) -> Set a -> f (Set b)
traverseSet f s = S.fromList <$> traverse f (S.toList s)

traverseMultiset :: (Applicative f, Ord b) => (a -> f b) -> MultiSet a -> f (MultiSet b)
traverseMultiset f s = M.fromList <$> traverse f (M.toList s)

data CtrlType = Regular | SupersetClosed deriving (Eq, Ord, Show)
data CtrlSetCtxt af = CSC
  { _cscType :: CtrlType
  , _cscCtxt :: MultiSet af
  } deriving (Eq, Ord, Show)

{-| A control set is a set of linear contexts made up of atomic formulas, that is,
    multisets of formulas of the bonding language.

    For a context C in a control set S we may want to consider its superset
    closure, that is, have that C' is in S for all superset C' of C.
    We therefore distinguish between superset-closed contexts and normal
    contexts in a control set. Actually, superset-closed contexts are the only
    way to specify infinite control sets.
-}
newtype CtrlSet af = CS
  { unCS :: Set (CtrlSetCtxt af)
  } deriving (Eq, Ord, Semigroup, Monoid, Show)

traverseCtrlSet :: (Applicative f, Ord b) => (a -> f b) -> CtrlSet a -> f (CtrlSet b)
traverseCtrlSet f (CS s) =
  CS <$> traverseSet (\(CSC ty ms) -> CSC ty <$> traverseMultiset f ms) s

fromCSCtxts :: (Foldable f, Ord af) => f (CtrlSetCtxt af) -> CtrlSet af
fromCSCtxts = CS . S.fromList . toList

toCtxtList :: CtrlSet af -> [CtrlSetCtxt af]
toCtxtList = toList . unCS

-- | Checks whether a linear context "respects" a control set context.
respectsCC :: Ord af => MultiSet af -> CtrlSetCtxt af -> Bool
respectsCC ms (CSC Regular ctxt) = ms /= ctxt
respectsCC ms (CSC SupersetClosed ctxt) = not (ctxt `isSubsetOf` ms)

-- | Checks whether a linear context "respects" a control set, that is,
-- if it respects all the control set contexts.
msRespectsCS :: Ord af => MultiSet af -> CtrlSet af  -> Bool
msRespectsCS ms = and . S.map (respectsCC ms) . unCS

-- | A reaction list is a list of pairs, where in each pair the first component
-- is an elementary base, and the second component is a control set.
newtype RList eb cs = RL
  { unRL :: [(eb, cs)]
  } deriving (Eq, Ord, Semigroup, Monoid, Show)

instance Bifunctor RList where
  bimap f g (RL xs) = RL (fmap (bimap f g) xs)

instance Bifoldable RList where
  bifoldMap f g (RL xs) = foldMap (bifoldMap f g) xs

instance Bitraversable RList where
  bitraverse f g (RL xs) = RL <$> traverse (bitraverse f g) xs

justCS :: Monoid eb => cs -> RList eb cs
justCS cs = RL [(mempty, cs)]

-- | Extends a reaction list with an elementary base.
extend :: Semigroup eb => eb -> RList eb cs -> RList eb cs
extend base = RL . map (first (base <>)) . unRL
-- was: extendRList

-- | Checks whether an elementary base "respects" a reaction list, given
-- a function to check whether the base "respects" the list's control sets.
respectsRList :: Semigroup eb => (eb -> cs -> Bool) -> eb -> RList eb cs -> Bool
respectsRList resp base = and . fmap (uncurry resp . first (base <>)) . unRL
