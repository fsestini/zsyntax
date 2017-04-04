module Filterable where

import qualified Data.Set as S
import Data.Either

class Filterable f where
  ffilter :: (a -> Bool) -> f a -> f a
  fpartitionEithers :: f (Either a b) -> (f a, f b)

fpartition :: (Filterable t) => (a -> Bool) -> t a -> (t a, t a)
fpartition p coll = (ffilter p coll, ffilter (not . p) coll)

filterOut :: (Functor f, Filterable f) => f (Maybe a) -> f a
filterOut coll = snd . fpartitionEithers $ fmap mapper coll
  where
    mapper Nothing = Left ()
    mapper (Just x) = Right x

instance Filterable [] where
  ffilter = filter
  fpartitionEithers = partitionEithers


-- class Collection f where
--   cconcat :: f (f a) -> f a
--   cmap :: (a -> b) -> f a -> f b
--   cadd :: a -> f a -> f a
--   cmerge :: f a -> f a -> f a

-- cconcatMap :: (Collection f) => (a -> f b) -> f a -> f b
-- cconcatMap f x = cconcat $ cmap f x

-- type Rule = Int
-- type ActiveSeq = Int

-- mix :: (Collection f) => f a -> f b -> f (a, b)
-- mix as bs = cconcatMap (\a -> cmap (\b -> (a, b)) bs) as

-- instance Collection [] where
--   cconcat = concat
--   cmap = map
--   cadd = (:)
--   cmerge = (++)

-- instance Collection S.Set where
--   cconcat s = S.foldr S.union S.empty s
