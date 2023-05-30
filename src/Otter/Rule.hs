module Otter.Rule where

import Data.Bifunctor (bimap)
import Control.Monad (MonadPlus(..), ap)
import Control.Applicative (Alternative(..))
import Data.Functor ((<&>))

{-| An inference rule schema is just a curried n-ary function where n is an
    unbounded, unspecified number of input premises, possibly zero (in that
    case, the rule is an axiom). A 'Rule' element may represent three possible
    situations:

    1. A failing computation which produces nothing; this is the degenerate case
       of a rule schema that always fails to match, and also what enables to
       make 'Rule' an instance of 'Alternative', 'MonadPlus', and 'MonadFail'.
    2. A successful computation that produces a 0-ary function, i.e. an axiom;
    3. A successful computation that produces a unary function, that is,
       a function accepting one argument and possibly returning a new 'Rule'.
       Applying such a function to an input corresponds to "matching"
       the first premise of the rule schema against a candidate input.
       The result is either a matching failure or a new, partially applied
       rule.
 -}
newtype Rule a b = Rule { unRule :: Maybe (Either b (a -> Rule a b)) }
type ProperRule a b = a -> Rule a b

-- | Constructs a single-premise rule from a matching function. 
match :: (a -> Maybe b) -> Rule a b
match p = Rule . Just . Right $ Rule . fmap Left . p

apply :: ProperRule a b -> a -> ([b], [ProperRule a b])
apply f = maybe mempty (either ((,[]) . pure) (([],) . pure)) . unRule . f

instance Functor (Rule a) where
  fmap f rel = rel <&> f

instance Applicative (Rule a) where
  pure = Rule . Just . Left
  (<*>) = ap

instance Monad (Rule a) where
  (Rule rel) >>= f =
    Rule $ rel >>= either (unRule . f) (Just . Right . fmap (>>= f))

instance Alternative (Rule a) where
  empty = Rule Nothing
  (Rule Nothing) <|> rel = rel
  rel <|> _ = rel

instance MonadPlus (Rule a) where

instance MonadFail (Rule a) where
  fail _ = Rule Nothing

arrowDimap :: (a -> b) -> (c -> d) -> (b -> c) -> (a -> d)
arrowDimap f g h x = g (h (f x))

-- This is just 'dimap' from the 'Profunctor' typeclass, but defined here
-- standalone to avoid pulling in profunctors for just a couple of uses of
-- 'dimap'.
relDimap :: (a -> b) -> (c -> d) -> Rule b c -> Rule a d
relDimap f g = Rule . fmap (bimap g (arrowDimap f (relDimap f g))) . unRule
