module Otter.SearchRes
  ( SearchRes
  , FailureReason(..)
  ) where

-- | Type representing the result of proof search.
type SearchRes a = Either FailureReason a

-- | Type of reasons why no result can be extracted from a search result stream.
-- 
-- Either the search space has been exhaustively searched and no result was
-- found (the query is not a theorem), or the search was terminated preemptively
-- according to an upper bound imposed on the maximum depth of the search space.
data FailureReason = NotATheorem | SpaceTooBig deriving (Eq, Show)
