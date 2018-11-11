module Otter.Relation where

import Data.Bifunctor
import Control.Monad
import Control.Monad.Fail
import Control.Applicative

{-| A Rel object represents a curried function with an unbounded, unspecified
    number of input arguments, possibly zero.
    Rel elements live in the Maybe monad, so they represent three possible
    situations:

    1. A failing computation which produces nothing;
    2. A successful computation that produces a trivial curried function
       accepting zero arguments (that is, a single value of the return type);
    3. A successful computation that produces a curried function, that is
       a function accepting one argument and returning a new value of type Rel.
 -}
newtype Rule a b = Rule { unRule :: Maybe (Either b (a -> Rule a b)) }
type ProperRule a b = a -> Rule a b

match :: (a -> Maybe b) -> Rule a b
match p = Rule . Just . Right $ Rule . fmap Left . p

apply :: ProperRule a b -> a -> ([b], [ProperRule a b])
apply f = maybe mempty (either ((,[]) . pure) (([],) . pure)) . unRule . f

instance Functor (Rule a) where
  fmap f rel = rel >>= (return . f)

instance Applicative (Rule a) where
  pure = return
  (<*>) = ap

instance Monad (Rule a) where
  return = Rule . Just . Left
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

relDimap :: (a -> b) -> (c -> d) -> Rule b c -> Rule a d
relDimap f g = Rule . fmap (bimap g (arrowDimap f (relDimap f g))) . unRule
