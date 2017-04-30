{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

module SFormula
  ( SFormula(..)
  , Sequent(..)
  , neutralize
  , fromLFormula
  , BioFormula(..)
  ) where

import Formula
import TypeClasses (PickMonad(..))
import Control.Monad
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- Simple formulas

-- | Type of simple formulas.
data SFormula a
  = SAtom (BioFormula a)
  | SConj (SFormula a)
          (SFormula a)
  | SImpl (SFormula a)
          (SFormula a)
  deriving (Eq, Ord)

fromLFormula :: LFormula p l a -> SFormula a
fromLFormula (FAtom (LBAtom atom)) = SAtom atom
fromLFormula (FAtom (RBAtom atom)) = SAtom atom
fromLFormula (FConj f1 f2 _) = fromLFormula f1 `SConj` fromLFormula f2
fromLFormula (FImpl f1 f2 _) = fromLFormula f1 `SImpl` fromLFormula f2

--------------------------------------------------------------------------------
-- Sequents.

data Sequent a = SQ (S.Set (SFormula a)) [SFormula a] (SFormula a)

neutralize :: (PickMonad m l, Ord a, Ord l) => Sequent a -> m (NeutralSequent l a)
neutralize (SQ unrestr linear concl) = do
  lUnrestr <- fmap S.fromList $ mapM toLabelled (S.toList unrestr)
  (moreLinear, (ORSLF lConcl)) <- rightAsync concl
  lLinear <- mapM leftAsync linear
  return $ NSQ lUnrestr (join lLinear) lConcl

toLabelled :: PickMonad m l => SFormula a -> m (OLFormula l a)
toLabelled (SAtom atom) = return (OLF (FAtom (LBAtom atom)))
toLabelled (SConj f1 f2) = do
  (OLF f1') <- toLabelled f1
  (OLF f2') <- toLabelled f2
  l <- pick
  return (OLF (FConj f1' f2' l))
toLabelled (SImpl f1 f2) = do
  (OLF f1') <- toLabelled f1
  (OLF f2') <- toLabelled f2
  l <- pick
  return (OLF (FImpl f1' f2' l))

rightAsync
  :: PickMonad m l
  => SFormula a -> m ([SFormula a], ORSLFormula l a)
rightAsync (SAtom atom) = return ([], ORSLF (FAtom (LBAtom atom)))
rightAsync (SConj f1 f2) = do
  (OLF f1') <- toLabelled f1
  (OLF f2') <- toLabelled f2
  l <- pick
  return ([], ORSLF (FConj f1' f2' l))
rightAsync (SImpl f1 f2) = do
  (ctxt, concl) <- rightAsync f2
  return (f1 : ctxt, concl)

leftAsync :: PickMonad m l => SFormula a -> m [OLSLFormula l a]
leftAsync (SAtom atom) = return [OLSLF (FAtom (LBAtom atom))]
leftAsync (SConj f1 f2) = liftM2 (++) (leftAsync f1) (leftAsync f2)
leftAsync (SImpl f1 f2) = do
  (OLF f1') <- toLabelled f1
  (OLF f2') <- toLabelled f2
  l <- pick
  return [OLSLF (FImpl f1' f2' l)]
