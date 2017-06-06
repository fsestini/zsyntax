{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module LinearContext.LinearCtxt
  ( LinearCtxt
  , NonEmptyLinearCtxt
  , module Context
  , neSubCtxtOf
  , toLC
  , fromLC
  , match
  , toNEList
  , fromNEList
  , mapNELC
  ) where

import Context
import qualified Data.List.NonEmpty as NE
import qualified Data.NonEmpty as DNE
import qualified Data.NonEmpty.Map as NEM
import Data.Semigroup
import Data.Maybe (isJust, fromMaybe)
import Control.Monad
import Control.Arrow ((>>>))
import qualified Data.Map as M
import qualified TypeClasses as T (Pretty(..), CanMap(..), prettys)
import Data.List (intersperse)
import LinearContext.PosInt
import Data.Foldable (toList)

--------------------------------------------------------------------------------
-- Linear contexts

newtype LinearCtxt a =
  LC { unLC :: M.Map a PosInt}
  deriving (Eq, Ord, Show)

instance Foldable LinearCtxt where
  foldr f z (LC lc) = foldr f z listed
    where
      listed = M.foldMapWithKey (\x y -> repeatN x y) lc

lcSubCtxtOf :: (Ord a) => LinearCtxt a -> LinearCtxt a -> [a]
lcSubCtxtOf (LC m1) (LC m2) =
  if m1 == m2
    then []
    else concatMap duane (M.toList m1) -- and $ map duane (M.toList m1)
  where
    duane (key, pi1) =
      flip (maybe (repeatN key pi1)) (M.lookup key m2) $ \pi2 ->
        take (toInt pi2 - toInt pi1) (repeat key)

instance Ord a => Monoid (LinearCtxt a) where
  mempty = LC M.empty
  (LC map1) `mappend` (LC map2) = LC $ M.unionWith piSum map1 map2

instance Ord a => Semigroup (LinearCtxt a) where
  lc1 <> lc2 = lc1 `mappend` lc2

instance (Ord a) => Context (LinearCtxt a) where
  type Elems (LinearCtxt a) = a
  add x (LC lc) = LC (M.insertWith piSum x piOne lc)
  singleton x = (LC (M.singleton x piOne))
  subCtxtOf = lcSubCtxtOf
  asFoldable f lc = f lc

instance T.Pretty a => T.Pretty (LinearCtxt a) where
  pretty = T.prettys

instance T.CanMap LinearCtxt where
  type Constr LinearCtxt x = Ord x
  map f (LC m) = LC (M.mapKeys f m)

----------------------------------------

matchMap
  :: Ord elem
  => M.Map elem PosInt -> M.Map elem PosInt -> Maybe (M.Map elem PosInt)
matchMap m m' = foldM (flip (uncurry matchElem)) m' (M.toList m)

matchElem
  :: Ord elem
  => elem -> PosInt -> M.Map elem PosInt -> Maybe (M.Map elem PosInt)
matchElem x n m = do
  M.lookup x m >>= guard . (n <=)
  return (M.update (flip piMinus n) x m)

{-| Match a context against another, returning the result if matching
    is successful. In particular
    * if c1 <= c2, then match c1 c2 = return (c2 \ c1)
    * otherwise, match c1 c2 = fail
-}
match
  :: Ord elem
  => LinearCtxt elem
  -> LinearCtxt elem
  -> Maybe (LinearCtxt elem)
match (LC m) (LC m') = fmap LC (matchMap m m')

--------------------------------------------------------------------------------
-- Non-empty linear contexts

newtype NonEmptyLinearCtxt elem = NELC
  { unNELC :: NEM.T elem PosInt
  } deriving (Eq, Ord, Show)

toLC :: Ord a => NonEmptyLinearCtxt a -> LinearCtxt a
toLC = LC . NEM.flatten . unNELC

fromLC :: Ord a => LinearCtxt a -> Maybe (NonEmptyLinearCtxt a)
fromLC (LC m) = fmap NELC (NEM.fetch m)

instance Ord elem => Context (NonEmptyLinearCtxt elem) where
  type Elems (NonEmptyLinearCtxt elem) = elem
  add x nelc = mergeElem x piOne nelc
  singleton x = NELC (NEM.singleton x piOne)
  subCtxtOf = neSubCtxtOf
  asFoldable f nelc = f (toLC nelc)

instance Ord elem => Semigroup (NonEmptyLinearCtxt elem) where
  m1 <> m2 = merge m1 m2

neSubCtxtOf :: Ord a => NonEmptyLinearCtxt a -> NonEmptyLinearCtxt a -> [a]
neSubCtxtOf nelc1 nelc2 = subCtxtOf (toLC nelc1) (toLC nelc2)

toNEList :: NonEmptyLinearCtxt elem -> NE.NonEmpty elem
toNEList (NELC nelc) = a NE.:| (as ++ fromLC)
  where
    ((x,n), lc) = NEM.minViewWithKey nelc
    (a NE.:| as) = repeatNE x n
    fromLC = toList (LC lc)

fromNEList :: Ord elem => NE.NonEmpty elem -> NonEmptyLinearCtxt elem
fromNEList (x NE.:| xs) = foldr add (singleton x) xs

mapNELC :: Ord b => (a -> b) -> NonEmptyLinearCtxt a -> NonEmptyLinearCtxt b
mapNELC f = fromNEList . NE.map f . toNEList

----------------------------------------

mergeElem
  :: Ord elem
  => elem -> PosInt -> NonEmptyLinearCtxt elem -> NonEmptyLinearCtxt elem
mergeElem x n (NELC m)
  | isJust $ NEM.lookup x m = NELC (NEM.mapWithKey mapper m)
  | otherwise = NELC (NEM.union (NEM.singleton x n) m)
  where
    mapper y i
      | x == y = piSum n i
      | otherwise = i

merge
  :: Ord elem
  => NonEmptyLinearCtxt elem
  -> NonEmptyLinearCtxt elem
  -> NonEmptyLinearCtxt elem
merge (NELC m) nelc = foldr (uncurry mergeElem) nelc (M.toList . NEM.flatten $ m)
