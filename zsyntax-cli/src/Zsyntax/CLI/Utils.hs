module Zsyntax.CLI.Utils where

import Data.List.NonEmpty (NonEmpty)

eToM :: Either a b -> Maybe b
eToM = either (const Nothing) Just

maybe' :: Maybe a -> b -> (a -> b) -> b
maybe' m x f = maybe x f m

foldMap1 :: Semigroup s => (a -> s) -> NonEmpty a -> s
foldMap1 f = foldr1 (<>) . fmap f
