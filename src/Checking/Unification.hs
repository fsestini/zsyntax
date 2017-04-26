{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Checking.Unification where

import Control.Arrow (first)
import Control.Monad.Trans.State
import Formula
import Checking.Generation (CanUnify(..))
import Checking.Constraints
import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.Trans

type Sub s l1 l2 = l1 -> Schema s l2

sub :: Sub s l1 l2 -> Schema s l1 -> Schema s l2
sub = (=<<)

infixl 5 <>
(<>) :: Sub s l1 l2 -> Sub s l2 l3 -> Sub s l1 l3
(<>) = (>=>)

unmoves :: (Eq s, Eq l) => Sub s l l -> l -> Bool
unmoves phi x = phi x == Label x

makeSub :: (Eq l) => l -> Schema s l -> Sub s l l
makeSub x sch y | x == y = sch
                | otherwise = return y

class Power s where
  splits :: s -> [(s, s)]
  power :: s -> [s]
  power = map fst . splits

unifyEquation
  :: (Power s, Show s, Eq s, Eq l)
  => Sub s l l -> EqConstraint s l -> [Sub s l l]
unifyEquation phi (VarConstr x sch)
  | unmoves phi x = return $ phi <> makeSub x (sub phi sch)
  | otherwise = unifyEquation phi (newEquation (phi x) (sub phi sch))
unifyEquation phi (SetConstr set sch) =
  case sch of
    (Label l) -> unifyEquation phi (VarConstr l (Set set))
    (Set set') ->
      if set == set'
        then return phi
        else [] -- fail "cannot unify `" ++ show set ++ "` with `" ++ show set'
    (Sum s1 s2) -> do
      (set1, set2) <- splits set
      unifyEquation phi (SetConstr set1 s1) >>=
        flip unifyEquation (SetConstr set2 s2)

newEquation :: Schema s l -> Schema s l -> EqConstraint s l
newEquation (Label l) sch = VarConstr l sch
newEquation (Set set) sch = SetConstr set sch
newEquation (Sum s1 s2) (Label l) = VarConstr l (Sum s1 s2)
newEquation (Sum s1 s2) (Set set) = SetConstr set (Sum s1 s2)
newEquation (Sum _ _) (Sum _ _) =
  error "cannot unify constraints of the form s1 + s2 = s3 + s4"

{-

StateT s m a

runStateT :: StateT s m a -> s -> m (a, s)

        -}

data UnifState l a = US
  { bioSub :: Sub (BiocoreSet a) l l
  , ctrlSub :: Sub (ControlSet a) l l
  }

newtype Unif l a b =
  U (StateT (UnifState l a) [] b)
  deriving (Functor, Applicative, Monad)

toStateMapB :: (Sub (BiocoreSet a) l l -> [Sub (BiocoreSet a) l l])
            -> UnifState l a
            -> [UnifState l a]
toStateMapB f st = do
  newSub <- f (bioSub st)
  return $ st { bioSub = newSub }

toStateMapC :: (Sub (ControlSet a) l l -> [Sub (ControlSet a) l l])
            -> UnifState l a
            -> [UnifState l a]
toStateMapC f st = do
  newSub <- f (ctrlSub st)
  return $ st { ctrlSub = newSub }

mapUnifState :: (UnifState l a -> [UnifState l a]) -> Unif l a ()
mapUnifState f = U (mapStateT (>>= ff) (return ()))
  where
    ff (x,i) = map ((,) x) (f i)

instance ( Power (BiocoreSet a)
         , Show (BiocoreSet a)
         , Eq l
         , Eq (BiocoreSet a)
         , Power (ControlSet a)
         , Show (ControlSet a)
         , Eq (ControlSet a)
         ) =>
         ConstraintMonad Unif l a where
  unifyB eq = mapUnifState (toStateMapB (flip unifyEquation eq))
  unifyC eq = mapUnifState (toStateMapC (flip unifyEquation eq))
