module ForwardSequent where

class ForwardSequent s where
  subsumes :: s -> s -> Bool
