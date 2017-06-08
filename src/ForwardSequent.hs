module ForwardSequent where

import TypeClasses (LogMonad(..))
import Data.Functor.Identity

class ForwardSequent s where
  subsumes :: (LogMonad m) => s -> s -> m Bool

subsumesBool :: ForwardSequent s => s -> s -> Bool
subsumesBool s1 s2 = runIdentity (subsumes s1 s2)
