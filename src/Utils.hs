module Utils where

import Data.Char
import Data.List

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
