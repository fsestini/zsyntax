{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Zsyntax.CLI.App (loopIO) where

import Text.Parsec.String (Parser)
import Data.Foldable (toList)
import Text.Parsec.Char (spaces)
import Data.List
import System.Console.Haskeline
import Control.Monad.State
import qualified Data.Map as M
import Data.Bifunctor
import System.IO
import Control.Monad.Except
import Lens.Micro.Platform
import Data.Text (Text, pack, unpack)

import Zsyntax.Formula
import Zsyntax.Labelled.Formula
import Zsyntax.Labelled.DerivationTerm (transitions)
import Zsyntax.Labelled.Rule
import Zsyntax.CLI.Utils
import Zsyntax.CLI.Structures
import Zsyntax.CLI.Execution
import Zsyntax.CLI.Command
-- import Zsyntax.Formula.BioFormula (prettyBioF)
import Control.Monad.Catch (MonadThrow, MonadMask, MonadCatch)

putStrLn' :: MonadIO m => String -> m ()
putStrLn' = liftIO . putStrLn

data AppState = AppState
  { _axEnv :: AxEnv
  , _tmEnv :: ThrmEnv
  , _searchConfig :: SearchConfig
--  , _searchLimit :: Int
  }
makeLenses ''AppState

instance HasAxEnv AppState where _AxEnv = axEnv
instance HasThrmEnv AppState where _ThrmEnv = tmEnv
instance HasSearchConfig AppState where _SearchConfig = searchConfig
  
-- Just a copy of what is defined in haskeline for Control.Monad.Trans.State
-- instance MonadException App where
--   controlIO f = App . StateT $ \s -> controlIO $ \(RunIO run) ->
--     let run' :: RunIO App
--         run' = RunIO (fmap (App . StateT . const) . run . flip runStateT s . unApp)
--     in fmap (flip runStateT s . unApp) $ f run'

newtype App a = App
  { unApp :: StateT AppState IO a
  } deriving (Functor, Applicative, Monad, MonadState AppState, MonadIO,
              MonadThrow, MonadCatch, MonadMask)

confirmReplace :: MonadIO m => String -> Name -> m () -> m ()
confirmReplace entity nm m = go
  where
    go = do
      answ <- liftIO $ do
        putStrLn (entity ++ " with name '" ++ nm ++ "' already exists.")
        putStr ("Replace? (yes/no) ")
        hFlush stdout
        getLine
      case answ of
        "yes" -> m
        "no"  -> pure ()
        s -> putStrLn' (s ++ " is not a valid answer.") >> go

prettyAggr :: Foldable f => f (BioFormula BioAtom) -> String
prettyAggr = prettys (ppBioFormula id)

printAxioms :: App ()
printAxioms = do
  env <- use axEnv -- get
  let axs = M.toList env
  mapM_ (putStrLn' . uncurry printAxiom) axs
  putStrLn' $ show (length axs) ++ " axioms in total."
  where printAxiom nm (AR fromAggr _ toAggr) =
          concat [nm, " : ", prettyAggr fromAggr, " -> ", prettyAggr toAggr]

printTheorems :: App ()
printTheorems = do
  thrms <- use tmEnv
  let ths = M.toList thrms
  mapM_ (putStrLn' . uncurry printTheorem . second fst) ths
  putStrLn' $ show (length ths) ++ " theorems in total."
  where printTheorem nm (QS _ from to') =
          concat [nm, " : ", prettyAggr from, prettyAggr to']

ppLSequent :: LSequent Atom Int -> String
ppLSequent (LS _ lc _ c) = concat
  [ concat (intersperse ","
             (fmap (unpack . withNeutral (ppLFormula (pack . ppAtom))) (toList lc)))
  , " ==> "
  , unpack $ ppLFormula (pack . ppAtom) c
  ]

printWhatFound :: MonadIO m => [LSequent Atom Int] -> m ()
printWhatFound seqs = liftIO $ do
  putStrLn "Some provable sequents: "
  mapM_ putStrLn (fmap ppLSequent . take 3 $ seqs)

ppTransition :: (LFormula Atom (), LFormula Atom ()) -> String
ppTransition (f1, f2) = pp f1 ++ " --> " ++ pp f2
  where pp = unpack . ppLFormula (pack . ppBioFormula id)

printQR :: MonadIO m => QueryResult -> m ()
printQR (Success (term ::: _)) = do
  putStrLn' ("Provable with " ++ show (length trans) ++ " transitions.")
  mapM_ (putStrLn' . ppTransition) trans
  where trans = transitions (void term)
printQR (Failure reason found) = do
  putStrLn' (reasonStr reason)
  printWhatFound found
  where reasonStr SpaceTooBig = "Reached search limit."
        reasonStr NotATheorem   = "Not a theorem."

printError :: MonadIO m => Error -> m ()
printError (AxNameClash nm) =
  putStrLn' ("Axiom '" ++ nm ++ "' already in scope. Abort.")
printError (ThrmNameClash nm) =
  putStrLn' ("Theorem '" ++ nm ++ "' already in scope. Abort.")
printError (AxNotInScope nm) =
  putStrLn' ("Axiom '" ++ nm ++ "' not in scope. Abort.")

loadFile :: FilePath -> App ()
loadFile path = do
  contents <- liftIO (readFile path)
  let commands =
        mapM (parseString (padded clicommand))
          (filter (not . null . trim) . lines $ contents)
  either
    (\pe -> liftIO (putStrLn $ "Error parsing file: " ++ show pe))
    (mapM_ execComm) commands
  where
    padded :: Parser a -> Parser a
    padded p = spaces *> p <* spaces
    isSpace = (== ' ')
    trim = dropWhileEnd isSpace . dropWhile isSpace

logError :: MonadIO m => ExceptT Error m () -> m ()
logError = join . fmap (either printError pure) . runExceptT

execComm :: CLICommand -> App ()
execComm (AddAxiom nm ax) =
  tryInsert _AxEnv nm ax >>=
    maybe (pure ()) (confirmReplace "Axiom" nm)
execComm (ChangeAxiom nm ax) = changeAxiom nm ax
execComm (RemoveAxioms axs) = removeAll _AxEnv axs
execComm (AddTheorem nm q) = logError $ do
  qr <- query q
  printQR qr
  case qr of
    Success (_ ::: sequent) ->
      saveTheorem nm q sequent >>= maybe (pure ()) (confirmReplace "Theorem" nm)
    _ -> pure ()
execComm (RemoveTheorems thms) = removeAll _ThrmEnv thms
execComm (RefreshTheorem tm) = logError $
  refreshTheorem tm >>= maybe (putStrLn' "No such theorem.") printQR
execComm (Query q) = logError $ query q >>= printQR
execComm (LoadFile p) = loadFile p
execComm (OpenFile _) = putStrLn' "Not implemented yet."
execComm (SaveToFile p) = do
  (axs, tms) <- (,) <$> use axEnv <*> use tmEnv
  let axComms = fmap (uncurry exportAxiom) (M.toList axs)
      tmComms = fmap (uncurry exportTheorem . second fst) (M.toList tms)
  liftIO . writeFile p $
    concat . (++ ["\n"]) . intersperse "\n" $ axComms ++ tmComms
execComm ListAxioms = printAxioms
execComm ListTheorems = printTheorems
execComm Clear = App (put initialState)
execComm (SetSearchLimit l) = searchConfig.cfgSearchLimit .= l
execComm Help =
  App . mapM_ putStrLn' $
  [ "list axioms        lists all available axioms"
  , "list theorems      list all stored theorems"
  , "add axiom name (from) (to) unless (constraints)"
  , "       adds new axiom"
  , "query [name] (from) (to) with [all axioms | axioms (...)]"
  , "       queries a sequent for validity"
  , "       if a name is specified, the successful query is stored"
  , "load file [path]   loads script file"
  , "save file [path]   saves current session to file"
  , "set search limit [num]"
  ]

initialState :: AppState
initialState = AppState mempty mempty cfg
  where cfg = SearchConfig { _cfgSearchLimit = 2000
                           , _cfgFoundListLen = 3
                           }

loop :: InputT App a
loop = do
  mline <- getInputLine ">>> "
  maybe' mline (pure ()) $ \line ->
    case parseString (spaces *> clicommand <* spaces) line of
      Left err -> outputStrLn (show err)
      Right c -> lift (execComm c)
  loop

loopIO :: IO ()
loopIO = fmap (fst . fst) . flip runStateT initialState . unApp . runInputT settings $ loop
  where
    wordList = [ "axiom", "axioms", "list", "query", "theorems", "unless", "clear" ]
    searchFun str = map simpleCompletion $ filter (str `isPrefixOf`) wordList
    settings = Settings (completeWord Nothing " \t" (pure . searchFun)) Nothing True
