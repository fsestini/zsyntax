module Utils where

import Data.Char
import Data.List

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

maySingleton :: [a] -> Maybe a
maySingleton [x] = Just x
maySingleton _ = Nothing
