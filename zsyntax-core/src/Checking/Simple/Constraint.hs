{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Checking.Simple.Constraint where

import Checking.Simple.World
import qualified Data.Set as S
import DerivationTerm
import Checking.Generation
import Control.Monad.Reader.Class
import LAFunctor

data SimpleConstr a =
  Respect (ElemBase a)
          (CtrlSet a)

check :: Ord a => SimpleConstr a -> Bool
check (Respect (EB base) (CS ctrlSet)) = S.null $ S.intersection base ctrlSet

data CtrlSetAnn r l a = WCS (CtrlSet a)

type WithCtrlSet l a = TriFix (AnnDerTerm :*: CtrlSetAnn)

instance TriFunctor CtrlSetAnn where

addCtrlSet :: AnnDerTerm l a -> WithCtrlSet l a
addCtrlSet = cata $ \termF -> case termF of
  (InitF _ :*: ann) -> Fix (termF :*: _)

-- generateConstraints
--   :: MonadReader (WorldInstance a) m
--   => AnnDerTerm l a -> m [SimpleConstr a]
-- generateConstraints = cataM $ \case
--   ((ImplLF d1 d2 _ _ _) :*: ann) -> _


  -- ImplLF (ctxt1, a) (ctxt2full, c) _ b _ -> do
  --   let ctxt2 = remove b ctxt2full
  --   undefined
    -- if isEmpty css1
    --   then do
    --     let ctxt = add (a `SImpl` b) (ctxt1 <> ctxt2)
    --         abCss = (CSS (S.singleton (a, b)))
    --     addBioConstraint (Respect ctxt2 abCss)
    --     return (ctxt, css2 <> abCss, c)
    --  else fail "ImplL must have empty control set in left premise"
