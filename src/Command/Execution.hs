{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}

module Command.Execution where

import TypeClasses (Pretty(..))
import Utils (trim)

import Command.Structures

import Control.Monad.Free
import Rules hiding (reprAx, AxRepr)
import Data.List
import Data.Bifunctor
import Control.Monad.Trans.State.Strict hiding (get, put)
import Control.Monad.State.Class
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Prover
import Control.Applicative (Alternative(..))
import Control.Monad.Trans.Except

type EUI a = ExceptT String (Free UIF) a

toUI :: a -> EUI a -> UI a
toUI x = (>>= either ((>> return x) . logUI) return) . runExceptT

toUI' :: (String -> UI b) -> (a -> UI b) -> EUI a -> UI b
toUI' f g = (>>= either f g) . runExceptT

tryInsertTheorem
  :: ThrmName
  -> (QueriedSeq frepr, ThrmShape ax)
  -> ThrmEnv frepr ax
  -> EUI (ThrmEnv frepr ax)
tryInsertTheorem nm@(TN name) (q, frml) thrms =
  maybe (throwE msg >> return thrms) return newThrms
  where
    newThrms = feInsert nm (q, Just frml) thrms
    msg = "theorem named '" ++ name ++ "' already present"

tryInsertAxiom
  :: ThrmName
  -> (AddedAxiom axr, ax)
  -> (AxEnv axr  ax)
  -> EUI (AxEnv axr ax)
tryInsertAxiom name@(TN nm) axiom env =
  maybe (throwE msg) return (feInsert name axiom env)
  where
    msg = "axiom named '" ++ nm ++ "' already present"

addAxiom
  :: CommAx axr ax
  => ThrmName
  -> axr
  -> (AxEnv axr ax)
  -> UI (AxEnv axr ax)
addAxiom name@(TN nm) axrepr env =
  case (reprAx axrepr) of
    Left err -> (logUI $ "parse error: " ++ (show err)) >> return env
    Right axiom ->
      case feInsert name (AAx axrepr, axiom) env of
        Just newEnv -> return newEnv
        Nothing ->
          logUI ("Axiom named '" ++ nm ++ "' already present") >> return env

addTheorem
  :: forall ax axr frepr.
     ( TransDerTerm (DerT ax axr frepr)
     , Search ax axr frepr
     , SrchConstr ax axr frepr
     )
  => ThrmName
  -> (QueriedSeq frepr)
  -> (AxEnv axr ax)
  -> ThrmEnv frepr ax
  -> Free UIF (ThrmEnv frepr ax)
addTheorem nm q env thrms =
  flip (toUI' ((>> return thrms) . logUI)) res $ \(impls, newThrms) -> do
    logUI ("provable with " ++ (show . length $ impls) ++ " transitions")
    forM_ impls (logUI . shower)
    return newThrms
  where
      -- shower :: TransRepr ax axr frepr -> String
      shower = pretty
      res :: EUI ([TransRepr (DerT ax axr frepr)], ThrmEnv frepr ax)
      res = do
        (DT dt ns) <-
          liftParse (queryToGoal env thrms q) >>= liftSR . runSearch
        newThrms <- tryInsertTheorem nm (q, fromRNS ns) thrms
        return (transitions dt, newThrms)

query
  :: ( TransDerTerm (DerT ax axr frepr)
     , Search ax axr frepr
     , SrchConstr ax axr frepr
     )
  => QueriedSeq frepr -> AxEnv axr ax -> ThrmEnv frepr ax -> UI ()
query q env thrms = flip (toUI' logUI) implsM $ \impls -> do
  logUI ("provable with " ++ (show . length $ impls) ++ " transitions")
  forM_ impls (logUI . shower)
  where
    shower = pretty
    implsM = fmap (transitions . term) $
      liftParse (queryToGoal env thrms q) >>= liftSR . runSearch

adjoinMsgEUI :: String -> EUI a -> EUI a
adjoinMsgEUI str = ExceptT . fmap (adjoinMsgE str) . runExceptT

adjoinMsgE :: String -> Either String a -> Either String a
adjoinMsgE str = first (str ++)

liftSR :: SearchRes a -> EUI a
liftSR (OkRes x) = return x
liftSR Saturated = ExceptT . return . Left $ "not provable: not a theorem"
liftSR ThresholdBreak =
  ExceptT . return . Left $ "not provable: search space too big"

data SearchRes a = OkRes a | Saturated | ThresholdBreak deriving (Functor)
instance Applicative SearchRes where
  pure = return
  (<*>) = ap
instance Monad SearchRes where
  return = OkRes
  (OkRes x) >>= f = f x
  Saturated >>= _ = Saturated
  ThresholdBreak >>= _ = ThresholdBreak
instance Alternative SearchRes where
  empty = mzero
  (<|>) = mplus
instance MonadPlus SearchRes where
  mzero = Saturated
  mplus (OkRes x) _ = OkRes x
  mplus Saturated x = x
  mplus ThresholdBreak x = x

instance SearchMonad SearchRes where
  failSaturated = Saturated
  failThresholdBreak = ThresholdBreak

liftParse :: Either String a -> EUI a
liftParse = ExceptT . return . (first ("parse error: " ++))

refreshTheorems
  :: (Search ax axr frepr, SrchConstr ax axr frepr)
  => StateT (AxEnv axr ax, ThrmEnv frepr ax) (Free UIF) ()
refreshTheorems = do
  (axioms, thrms) <- get
  newThrms <- lift $ refreshTheorems' axioms thrms
  put (axioms, newThrms)

refreshTheorems'
  :: forall frepr axr ax.
     (Search ax axr frepr, SrchConstr ax axr frepr)
  => (AxEnv axr ax) -> (ThrmEnv frepr ax) -> UI (ThrmEnv frepr ax)
refreshTheorems' axioms = processThrms doer
  where
    doer
      :: ThrmName
      -> (QueriedSeq frepr, Maybe (ThrmShape ax))
      -> ThrmEnv frepr ax
      -> UI (QueriedSeq frepr, Maybe (ThrmShape ax))
    doer (TN name) (q, _) thrms =
      fmap ((,) q) . toUI Nothing . fmap Just $
      adjoinMsgEUI ("theorem " ++ name ++ " failed: ") (doer' axioms thrms q)
    doer' :: AxEnv axr ax -> ThrmEnv frepr ax
          -> QueriedSeq frepr -> EUI (ThrmShape ax)
    doer' env thrms q = do
      actualSequent <- liftParse (queryToGoal env thrms q)
      (DT _ ns) <- liftSR (runSearch actualSequent)
      return (fromRNS ns)

type SrchPr term srchfr =
  (SearchTriple ((NSequent (Ax srchfr) srchfr (Cty srchfr)))
                (GoalNSequent (Ax srchfr) srchfr)
                (ResultNSequent (Ax srchfr) srchfr (Cty srchfr)))

type SrchConstr ax axr frepr =
  (
  SrchPr (DerT ax axr frepr) (SrchF ax axr frepr),
  Formula (SrchF ax axr frepr)
  , HasElemBase (SrchF ax axr frepr), HasControlType (SrchF ax axr frepr)
  , BaseCtrl (Eb (SrchF ax axr frepr)) (Cty (SrchF ax axr frepr))
  , DerTerm (DerT ax axr frepr) (SrchF ax axr frepr)
  , HasAxiom (SrchF ax axr frepr), Ord (DerT ax axr frepr)
  , Ord (Ax (SrchF ax axr frepr)))

type MyGNS ax axr frepr =
  GoalNSequent (Ax (SrchF ax axr frepr))
               (SrchF ax axr frepr)

type MySrchRes ax axr frepr =
  SearchRes (DT (DerT ax axr frepr)
    (ResultNSequent (Ax (SrchF ax axr frepr))
                    (SrchF ax axr frepr)
                    (Cty (SrchF ax axr frepr))))

runSearch
  :: (SrchConstr ax axr frepr)
  => MyGNS ax axr frepr -> MySrchRes ax axr frepr
runSearch neutral = (runIdentity . proverSearch initS initR) neutral
  where
    (initS, initR) = initialSequentsAndRules neutral

changeAxiom
  :: (CommAx axr ax)
  => ThrmName
  -> axr
  -> (AxEnv axr ax)
  -> UI (AxEnv axr ax)
changeAxiom axName axrepr axEnv = toUI axEnv $ do
  axiom <- liftParse (reprAx axrepr)
  let newAxEnv = feReplace axName (AAx axrepr, axiom) axEnv
  return newAxEnv

removeAxiom
  :: ThrmName
  -> (AxEnv axr ax)
  -> UI (AxEnv axr ax)
removeAxiom axName axEnv = do
  let newAxioms = feRemove axName axEnv
  return newAxioms

loadFile
  :: (MegaConstr axr ax frepr)
  => FilePath -> StateT (AxEnv axr ax, ThrmEnv frepr ax) (Free UIF) ()
loadFile path = do
  contents <- lift $ uiLoadFile path
  let commandsE =
        mapM parseCommand (filter (not . null . trim) . lines $ contents)
  case commandsE of
    Left err -> lift . logUI $ "error parsing the file: " ++ (show err)
    Right commands -> mapM_ execCommand commands

saveToFile
  :: (CPrint axr frepr)
  => FilePath -> AxEnv axr ax -> ThrmEnv frepr ax -> UI ()
saveToFile path axEnv thrms =
  uiSaveFile path . concat $ aux axStrs ++ aux thrmStrs
  where
    axStrs = printAxAll axEnv
    thrmStrs = printThrmAll thrms
    aux = (++ ["\n"]) . intersperse "\n"

--------------------------------------------------------------------------------
-- Generic command execution

type MegaConstr axr ax frepr =
  (CParse axr frepr, TransDerTerm (DerT ax axr frepr),
  CommAx axr ax, Search ax axr frepr,
  SrchConstr ax axr frepr, CPrint axr frepr)

liftUITrans
  :: (AxEnv axr ax -> ThrmEnv frepr ax -> UI (AxEnv axr ax, ThrmEnv frepr ax))
  -> StateT (AxEnv axr ax, ThrmEnv frepr ax) (Free UIF) ()
liftUITrans f = do
  (axs,thrms) <- get
  (newAxs, newThrms) <- lift $ f axs thrms
  put (newAxs, newThrms)

traversePair :: Applicative m => (m a, m b) -> m (a, b)
traversePair (x,y) = (,) <$> x <*> y

execCommand'
  :: (MegaConstr axr ax frepr) => Command axr frepr
  -> AxEnv axr ax
  -> ThrmEnv frepr ax
  -> UI (AxEnv axr ax, ThrmEnv frepr ax)
execCommand' c axEnv thrms = fmap snd $ runStateT (execCommand c) (axEnv, thrms)

execCommand
  :: (MegaConstr axr ax frepr)
  => Command axr frepr
  -> StateT (AxEnv axr ax, ThrmEnv frepr ax) (Free UIF) ()
execCommand (AddAxiom name axrepr) =
  liftUITrans (axToTrans $ addAxiom name axrepr) >> refreshTheorems
execCommand (ChangeAxiom name axrepr) =
  liftUITrans (axToTrans $ changeAxiom name axrepr) >> refreshTheorems
execCommand (RemoveAxiom name) =
  liftUITrans (axToTrans $ removeAxiom name) >> refreshTheorems
execCommand (AddTheorem name q) =
  liftUITrans (thrmToTrans $ addTheorem name q) >> refreshTheorems
execCommand (Query q) = get >>= lift . uncurry (query q)
execCommand (LoadFile path) = loadFile path >> refreshTheorems
execCommand (SaveToFile path) = get >>= lift . uncurry (saveToFile path)

axToTrans :: Monad m => (a1 -> m a) -> a1 -> b -> m (a, b)
axToTrans f = curry (traversePair . bimap f return)
thrmToTrans :: Functor f => (t -> a -> f b) -> t -> a -> f (t, b)
thrmToTrans f ax = fmap ((,) ax) . f ax
