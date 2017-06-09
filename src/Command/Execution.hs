{-# LANGUAGE StandaloneDeriving #-}
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

import TypeClasses (Pretty(..), PrettyK, prettys)
import Utils (trim, (&&&), (.:))

import Command.Structures

import Data.Bitraversable (bitraverse)
import Data.Foldable
import qualified Data.Set as S
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
import Parsing

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
  maybe ask return (feInsert nm newItem thrms)
  where
    ask = do
      answ <- lift $ uiAskReplaceThrm nm
      case answ of
        Yes -> return $ feReplace nm newItem thrms
        No ->
          throwE ("theorem named '" ++ name ++ "' already present") >>
          return thrms
    newItem = (q, Just frml)

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
     , Eq ax
     )
  => ThrmName
  -> (QueriedSeq frepr)
  -> (AxEnv axr ax)
  -> ThrmEnv frepr ax
  -> Free UIF (ThrmEnv frepr ax)
addTheorem nm q env thrms =
  flip (toUI' ((>> return thrms) . logUI)) res $ \(impls, newThrms) -> do
    logUI ("provable with " ++ (show . length $ impls) ++ " transitions")
    forM_ impls (logUI . pretty)
    return newThrms
  where
    res :: EUI ([TransRepr (DerT ax axr frepr)], ThrmEnv frepr ax)
    res = do
      goal <- liftParse (queryToGoal env thrms q)
      (DT dt ns) <- liftSRVerbose goal (runSearch goal)
      let usedAxNames = toNames env thrms . fmap toAx . toList . rnsUc $ ns
          m = mode . qsAxioms $ q
      q' <-
        case m of
          Normal -> return q
          Refine -> do
            lift $ logUI ("refined to axioms: " ++ prettys usedAxNames)
            return $ QS (QA (Some usedAxNames) m) (qsFrom q) (qsTo q)
      newThrms <- tryInsertTheorem nm (q', fromRNS ns) thrms
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
    implsM = do
      goal <- liftParse (queryToGoal env thrms q)
      t <- liftSRVerbose goal (runSearch goal)
      return (transitions . term $ t)
    -- implsM = fmap (transitions . term) $
    --   liftParse (queryToGoal env thrms q) >>= liftSR . runSearch

adjoinMsgEUI :: String -> EUI a -> EUI a
adjoinMsgEUI str = ExceptT . fmap (adjoinMsgE str) . runExceptT

adjoinMsgE :: String -> Either String a -> Either String a
adjoinMsgE str = first (str ++)

mayStdErr :: Maybe String -> Free UIF ()
mayStdErr Nothing = return ()
mayStdErr (Just x) = uiStdErr x

liftSR :: (Maybe String, SearchRes seqty a) -> EUI a
liftSR (msg, res) =
  lift (mayStdErr msg) >>
  case res of
    (OkRes x) -> return x
    (Saturated _) -> ExceptT . return . Left $ "not provable: not a theorem"
    (ThresholdBreak _) ->
      ExceptT . return . Left $ "not provable: search space too big"

liftSRVerbose
  :: (Search ax axr frepr, SearchDump ax axr frepr)
  => MyGoalNSequent ax axr frepr
  -> (Maybe String, SearchRes (MyDTS ax axr frepr) a)
  -> EUI a
liftSRVerbose goal (msg, x) =
  lift (mayStdErr msg) >>
  case x of
    OkRes res -> return res
    Saturated seqs ->
      let msg' = "not provable: not a theorem\n" ++ dump seqs
      in outMsg msg'
    ThresholdBreak seqs ->
      let msg' = "not provable: search space too big\n" ++ dump seqs
      in outMsg msg'
  where
    outMsg = ExceptT . return . Left
    dump seqs =
      let toPrint = (take 3 . sortSeqs $ seqs)
      in if null toPrint
           then ""
           else (("Some provable reactions were:\n" ++) .
                 pprintSeqs . take 3 . sortSeqs $
                 seqs)
    pprintSeqs = concat . intersperse "\n" . fmap (flip pprintSeq goal)
    sortSeqs =
      fmap fst .
      filter ((> 0) . snd) .
      sortBy (\p1 p2 -> compare (snd p1) (snd p2)) .
      fmap (\s -> (s, goalDiff s goal)) . fmap payload . toList

data SearchRes seqty a
  = OkRes a
  | Saturated (S.Set seqty)
  | ThresholdBreak (S.Set seqty)
  deriving (Functor)

instance Applicative (SearchRes seqty) where
  pure = return
  (<*>) = ap
instance Monad (SearchRes seqty) where
  return = OkRes
  (OkRes x) >>= f = f x
  (Saturated x) >>= _ = Saturated x
  (ThresholdBreak x) >>= _ = ThresholdBreak x
instance Alternative (SearchRes seqty) where
  empty = mzero
  (<|>) = mplus
instance MonadPlus (SearchRes seqty) where
  mzero = Saturated S.empty
  mplus (OkRes x) _ = OkRes x
  mplus (Saturated _) x = x
  mplus (ThresholdBreak _) x = x

instance SearchMonad seqty (SearchRes seqty) where
  failSaturated seqs = Saturated seqs
  failThresholdBreak seqs = ThresholdBreak seqs

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
  ( SrchPr (DerT ax axr frepr) (SrchF ax axr frepr)
  , Formula (SrchF ax axr frepr)
  , Pretty (Ax (SrchF ax axr frepr))
  , PrettyK (SrchF ax axr frepr)
  , SearchDump ax axr frepr
  , HasElemBase (SrchF ax axr frepr), HasControlType (SrchF ax axr frepr)
  , BaseCtrl (Eb (SrchF ax axr frepr)) (Cty (SrchF ax axr frepr))
  , DerTerm (DerT ax axr frepr) (SrchF ax axr frepr)
  , HasAxiom (SrchF ax axr frepr), Ord (DerT ax axr frepr)
  , Ord (Ax (SrchF ax axr frepr)))

type MyGNS ax axr frepr =
  GoalNSequent (Ax (SrchF ax axr frepr))
               (SrchF ax axr frepr)

-- type MyNSequent ax axr frepr =
--   NSequent (Ax (SrchF ax axr frepr))
--                  (SrchF ax axr frepr)
--                  (Cty (SrchF ax axr frepr))

type MySrchRes ax axr frepr =
  (Maybe String, SearchRes (DT (DerT ax axr frepr) (MyNSequent ax axr frepr))
    (DT (DerT ax axr frepr)
        (ResultNSequent (Ax (SrchF ax axr frepr))
                        (SrchF ax axr frepr)
                        (Cty (SrchF ax axr frepr)))))

type MyDTS ax axr frepr = DT (DerT ax axr frepr) (MyNSequent ax axr frepr)

runSearch
  :: forall ax axr frepr . (SrchConstr ax axr frepr)
  => MyGNS ax axr frepr -> MySrchRes ax axr frepr
runSearch neutral =
  ((const Nothing) &&& runIdentity . (srch initS initR)) neutral
  where
    (initS :: S.Set (MyDTS ax axr frepr), initR) =
      initialSequentsAndRules neutral
    srch = proverSearch

changeAxiom
  :: (CommAx axr ax)
  => ThrmName -> axr -> (AxEnv axr ax) -> UI (AxEnv axr ax)
changeAxiom axName axrepr axEnv = toUI axEnv $ do
  axiom <- liftParse (reprAx axrepr)
  let newAxEnv = feReplace axName (AAx axrepr, axiom) axEnv
  return newAxEnv

loadFile
  :: (MegaConstr axr ax frepr)
  => FilePath -> StateT (AxEnv axr ax, ThrmEnv frepr ax) (Free UIF) ()
loadFile path = do
  contents <- lift $ uiLoadFile path
  let commandsE =
        mapM
          (parseString (padded pCommand))
          (filter (not . null . trim) . lines $ contents)
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
  SrchConstr ax axr frepr, CPrint axr frepr, Eq ax)

liftUITrans
  :: (AxEnv axr ax -> ThrmEnv frepr ax -> UI (AxEnv axr ax, ThrmEnv frepr ax))
  -> StateT (AxEnv axr ax, ThrmEnv frepr ax) (Free UIF) ()
liftUITrans f = do
  (axs,thrms) <- get
  (newAxs, newThrms) <- lift $ f axs thrms
  put (newAxs, newThrms)

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
  liftUITrans (traverseFst $ addAxiom name axrepr) >> refreshTheorems
execCommand (ChangeAxiom name axrepr) =
  liftUITrans (traverseFst $ changeAxiom name axrepr) >> refreshTheorems
execCommand (RemoveAxioms axNames) =
  liftUITrans (traverseFst $ removeAll axNames) >> refreshTheorems
execCommand (AddTheorem name q) =
  liftUITrans (\x -> fmap ((,) x) . (addTheorem name q) x) >> refreshTheorems
execCommand RefreshTheorems = refreshTheorems
execCommand (RemoveTheorems thNames) =
  liftUITrans (curry (bitraverse pure (removeAll thNames))) >> refreshTheorems
execCommand (Query q) = get >>= lift . uncurry (query q)
execCommand (LoadFile path) = loadFile path >> refreshTheorems
execCommand (OpenFile path) = put (feEmpty, feEmpty) >> loadFile path
execCommand (SaveToFile path) = get >>= lift . uncurry (saveToFile path)

traverseFst :: Applicative m => (a1 -> m a) -> a1 -> b -> m (a, b)
traverseFst f = curry (bitraverse f pure)

removeAll :: FEnv env => [ThrmName] -> env -> UI env
removeAll = flip (foldM (flip (return .: feRemove)))
