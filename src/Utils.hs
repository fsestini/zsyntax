module Utils where

import Data.Char
import Data.List
import Control.Monad
import qualified Data.List.NonEmpty as NE
import Data.Semigroup

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

maySingleton :: [a] -> Maybe a
maySingleton [x] = Just x
maySingleton _ = Nothing

infix 8 .:
(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(f .: g) x y = f (g x y)

infix 8 &&&
(&&&) :: (a -> b) -> (a -> c) -> a -> (b,c)
(f &&& g) x = (f x, g x)

uncurry3 f (x,y,z) = f x y z

discardResP :: (Monad m, MonadPlus p) => m a -> m (p b)
discardResP m = m >> return mzero

foldMap1 :: Semigroup s => (a -> s) -> NE.NonEmpty a -> s
foldMap1 f = foldr1 (<>) . fmap f
