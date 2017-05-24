module LinearContext.PosInt
  ( PosInt
  , piOne
  , piSum
  , piMinus
  , repeatN
  , repeatNE
  ) where

import Data.Semigroup
import qualified Data.List.NonEmpty as NE

newtype PosInt = PI Int deriving (Eq, Ord, Show)

piOne :: PosInt
piOne = PI 1

piSucc :: PosInt -> PosInt
piSucc (PI i) = PI (i + 1)

piSum :: PosInt -> PosInt -> PosInt
piSum (PI n) (PI m) = PI (n + m)

piMinus :: PosInt -> PosInt -> Maybe PosInt
piMinus (PI n) (PI m) | n - m > 0 = Just (PI (n - m))
                      | otherwise = Nothing

instance Semigroup PosInt where
  (PI n) <> (PI m) = PI (n + m)

repeatN :: a -> PosInt -> [a]
repeatN x (PI i) = take i $ repeat x

repeatNE :: a -> PosInt -> NE.NonEmpty a
repeatNE x (PI 1) = x NE.:| []
repeatNE x (PI n) = x NE.:| take (n-1) (repeat x)
