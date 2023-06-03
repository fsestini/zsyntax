{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Zsyntax.CLI.Execution
  ( QueryResult(..)
  , FailureReason(..)
  , HasSearchConfig(..)
  , SearchConfig(..)
  , cfgSearchLimit
  , cfgFoundListLen
  , query
  , tryInsert
  , saveTheorem
  , refreshTheorem
  , removeAll
  , changeAxiom
  ) where

import Data.Function (on)
import Data.List (sortBy)
import Data.Maybe (isJust)
import Data.Foldable (toList)
import Control.Monad.State
import Control.Monad.Except
import Data.Map (Map)
import qualified Data.Map as M
import Lens.Micro.Platform (Lens', set, use, (^.), (%=), makeLenses)

import Zsyntax ( Sequent, SearchRes, FailureReason(..), axForget)
import qualified Zsyntax as Z (search, SearchOutput(..))
import Zsyntax.Labelled.DerivationTerm
import Zsyntax.Labelled.Rule
import Zsyntax.CLI.Structures

--------------------------------------------------------------------------------

search :: Int -> Sequent Atom
              -> (SearchRes (DerivationTerm Atom Int ::: LSequent Atom Int),
                 [LSequent Atom Int],
                 GoalNSequent Atom Int)
search i s = (res, srcd, Z.labelledGoal searchRes)
  where
    -- g = toLabelledGoal s
    searchRes = Z.search s i
    res = Z.otterResult searchRes
    srcd = map _payload (Z.searchedSequents searchRes)
    -- (res, srcd) = bimap (Z.extractResults i) (fmap _payload) searchRes

--------------------------------------------------------------------------------

mHas :: Ord k => k -> Map k v -> Bool
mHas k = isJust . M.lookup k

-- type Transition = (SFormula () Atom , SFormula () Atom)

tryInsert :: MonadState s m
          => Lens' s (Map Name a) -> Name -> a -> m (Maybe (m ()))
tryInsert l name x = do
  b <- mHas name <$> use l
  if b then pure (Just action) else action >> pure Nothing
  where action = l %= M.insert name x

-- prettyTransition :: Transition -> String
-- prettyTransition (f1, f2) =
--   prettySF (prettyBioF id) f1 ++ " --> " ++ prettySF (prettyBioF id) f2

usedAxs :: MonadZState s m => LSequent Atom Int -> m [Name]
usedAxs = toAxNames . fmap axForget . toList . lsUCtxt

-- data ResInfo = ResInfo
--   { _riTrans :: [Transition]
--   , _riSeq :: NeutralSequent
--   , _riUsedAxs :: [Name]
--   }
-- data QueryResult = QueryResult
--   { _qResult :: Either [ResInfo] [ResInfo]
--   , _qSearched :: [NeutralSequent]
--   }
-- makeLenses ''ResInfo
-- makeLenses ''QueryResult

-- switchResult :: b -> b -> (ResInfo -> b) -> Either [ResInfo] [ResInfo] -> b
-- switchResult x _ f (Left xs) = maybe x f (listToMaybe xs)
-- switchResult _ y f (Right xs) = maybe y f (listToMaybe xs)

-- querySuccess :: QueryResult -> Maybe ResInfo
-- querySuccess = either listToMaybe listToMaybe . _qResult

-- query :: Int -> QueriedSeq -> AxEnv -> ThrmEnv -> Either Error QueryResult
-- query limit q axs ths = do
--   goal <- queryToGoal axs ths q
--   let (res, srchd, lgoal) = search limit goal
--       f = fmap (\(dt ::: ns) -> ResInfo (transitions dt) ns (usedAxs axs ths ns))
--   pure $ QueryResult (bimap f f res)
--     (sortBy (flip compare `on` (`goalDiff` lgoal)) srchd)

data SearchConfig = SearchConfig
  { _cfgSearchLimit :: Int
  , _cfgFoundListLen :: Int
  }
makeLenses ''SearchConfig

class HasSearchConfig s where
  _SearchConfig :: Lens' s SearchConfig

data QueryResult =
    Success (DerivationTerm Atom Int ::: LSequent Atom Int)
  | Failure FailureReason [LSequent Atom Int]

query :: (MonadZState s m, HasSearchConfig s, MonadError Error m)
      => QueriedSeq
      -> m QueryResult
query q = do
  cfg <- use _SearchConfig
  goal <- queryToGoal q
  let (res, searched, lgoal) = search (_cfgSearchLimit cfg) goal
  case res of
    Right x -> pure (Success x)
    Left reason ->
      let results =
            take (_cfgFoundListLen cfg)
                 (sortBy (flip compare `on` (`goalDiff` lgoal)) searched)
      in pure (Failure reason results)
             
-- Given a list of axioms that have been modified, it invalidates all
-- theorems that depend on some of these axioms.
invalidateAffectedTheorem :: (MonadState s m, HasThrmEnv s) => Name -> m ()
invalidateAffectedTheorem nm =
  _ThrmEnv %= fmap (\(q, m) ->
      if f (q ^. qsAxioms.requiredAxs) then (q, Nothing) else (q, m))
  where
    f (Some nms) = nm `elem` nms
    f AllOfEm = True

refineQueriedSeq
  :: MonadZState s m => QueriedSeq -> LSequent Atom Int -> m QueriedSeq
refineQueriedSeq qs sequent = 
  case qs ^. qsAxioms.axMode of
    Normal -> pure qs
    Refine -> do
      axs <- Some <$> usedAxs sequent
      pure $ set (qsAxioms.requiredAxs) axs qs

saveTheorem
  :: MonadZState s m
  => Name
  -> QueriedSeq
  -> LSequent Atom Int
  -> m (Maybe (m ()))
saveTheorem name qs sequent = do
  qs' <- refineQueriedSeq qs sequent
  tryInsert _ThrmEnv name (qs', fromNS sequent)

-- Tries to establish a previously invalidated theorem with the
-- current state. It returns the result of the query (possibly
-- updating the internal state if successful), or 'Nothing' if no such
-- invalidated theorem exists.
refreshTheorem
  :: (MonadError Error m, MonadZState s m, HasSearchConfig s)
  => Name -> m (Maybe QueryResult)
refreshTheorem name =
  M.lookup name <$> use _ThrmEnv >>= \case
    Just (q, Nothing) -> do
      res <- query q
      case res of
        Success (_ ::: sequent) -> do
          _ThrmEnv %= M.insert name (q, fromNS sequent)
        _ -> pure ()
      pure (Just res)
    _ -> pure Nothing

removeAll :: (Ord k, MonadState s m) => Lens' s (Map k v) -> [k] -> m ()
removeAll l = sequence_ . fmap ((l %=) . M.delete)

changeAxiom :: MonadZState s m => Name -> AxRepr -> m ()
changeAxiom nm ax =
  changeEnv _AxEnv nm ax >> invalidateAffectedTheorem nm

changeEnv :: (Ord k, MonadState s m) => Lens' s (Map k v) -> k -> v -> m ()
changeEnv l nm ax = l %= M.adjust (const ax) nm
