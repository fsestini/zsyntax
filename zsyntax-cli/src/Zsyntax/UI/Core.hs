{-# LANGUAGE GeneralizedNewtypeDeriving, DerivingStrategies, FlexibleInstances,
  MultiParamTypeClasses, DeriveFunctor, TemplateHaskell #-}

module Zsyntax.UI.Core where

import Prelude hiding (readFile, writeFile)

import Control.Monad.Free (Free(..), wrap)
import Control.Monad.State (MonadState(..))
import Lens.Micro.Platform (makeLenses, use, (.=))
import qualified Data.Map as M (toList)
import Data.Bifunctor (second)
import qualified Data.List as L (intersperse, dropWhileEnd)
import Data.Text (pack, unpack)
import Text.Parsec (ParseError, spaces)
import Text.Parsec.String (Parser)
import Control.Monad.Except

import Zsyntax.CLI.Structures
import Zsyntax.CLI.Command
  (prettys, CLICommand(..), parseString, clicommand, exportAxiom, exportTheorem)
import Zsyntax.CLI.Execution
  ( QueryResult(..), SearchConfig(..), HasSearchConfig(..), tryInsert
  , changeAxiom, removeAll, query, saveTheorem, refreshTheorem, cfgSearchLimit)
import Zsyntax.Labelled.DerivationTerm (transitions)
import Zsyntax.Formula (BioFormula, ppBioFormula)
import Zsyntax.Labelled.Rule (LSequent(..), withNeutral, (:::)(..))
import Zsyntax.Labelled.Formula (LFormula, ppLFormula)
import Zsyntax (FailureReason(..))
import Data.Foldable (toList)

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

type FailureInfo = (FailureReason, [LSequent Atom Int])

data UIF a
  = PrintStr String a
  | GetStr (String -> a)
  | Get (AppState -> a)
  | Put AppState a
  | ProcessError Error a
  | ProcessQueryResult QueryResult a
  | ReadFile FilePath (String -> a)
  | WriteFile FilePath String a
  deriving Functor

newtype UI a = UI { unUI :: Free UIF a }
  deriving newtype (Functor, Applicative, Monad)

instance MonadState AppState UI where
  get = UI (wrap (Get pure))
  put s = UI (wrap (Put s (pure ())))

processError :: ExceptT Error UI () -> UI ()
processError =
  join . fmap (either (\e -> UI (wrap (ProcessError e (pure ())))) pure) . runExceptT

printStr :: String -> UI ()
printStr str = UI (wrap (PrintStr str (pure ())))

printStrLn :: String -> UI ()
printStrLn s = printStr (s ++ "\n")

getStr :: UI String
getStr = UI (wrap (GetStr pure))

processQueryResult :: QueryResult -> UI ()
processQueryResult r = UI (wrap (ProcessQueryResult r (pure ())))

readFile :: FilePath -> UI String
readFile fp = UI (wrap (ReadFile fp pure))

writeFile :: FilePath -> String -> UI ()
writeFile fp s = UI (wrap (WriteFile fp s (pure ())))

confirmReplace :: String -> Name -> UI () -> UI ()
confirmReplace entity nm m = do
  answ <- do
    printStrLn (entity ++ " with name '" ++ nm ++ "' already exists.")
    printStr ("Replace? (yes/no) ")
    -- hFlush stdout
    getStr
  case answ of
    "yes" -> m
    "no"  -> pure ()
    _ -> printStrLn ("invalid answer") >> confirmReplace entity nm m

prettyAggr :: Foldable f => f (BioFormula BioAtom) -> String
prettyAggr = prettys (ppBioFormula id)

printAxioms :: UI ()
printAxioms = do
  env <- use axEnv -- get
  let axs = M.toList env
  mapM_ (printStrLn . uncurry printAxiom) axs
  printStrLn $ show (length axs) ++ " axioms in total."
  where printAxiom nm (AR fromAggr _ toAggr) =
          concat [nm, " : ", prettyAggr fromAggr, " -> ", prettyAggr toAggr]

printTheorems :: UI ()
printTheorems = do
  thrms <- use tmEnv
  let ths = M.toList thrms
  mapM_ (printStrLn . uncurry printTheorem . second fst) ths
  printStrLn $ show (length ths) ++ " theorems in total."
  where printTheorem nm (QS _ from to') =
          concat [nm, " : ", prettyAggr from, prettyAggr to']

printWhatFound :: [LSequent Atom Int] -> UI ()
printWhatFound seqs = do
  printStrLn "Some provable sequents: "
  mapM_ printStrLn (fmap ppLSequent $ seqs)

  where
    ppLSequent :: LSequent Atom Int -> String
    ppLSequent (LS _ lc _ c) = concat
      [ concat (L.intersperse ","
                 (fmap (unpack . withNeutral (ppLFormula (pack . ppAtom))) (toList lc)))
      , " ==> "
      , unpack $ ppLFormula (pack . ppAtom) c
      ]

ppTransition :: (LFormula Atom (), LFormula Atom ()) -> String
ppTransition (f1, f2) = pp f1 ++ " --> " ++ pp f2
  where pp = unpack . ppLFormula (pack . ppBioFormula id)

printQR :: QueryResult -> UI ()
printQR (Success (term ::: _)) = do
  printStrLn ("Provable with " ++ show (length trans) ++ " transitions.")
  mapM_ (printStrLn . ppTransition) trans
  where trans = transitions (void term)
printQR (Failure reason found) = do
  printStrLn (reasonStr reason)
  printWhatFound found
  where reasonStr SpaceTooBig = "Reached search limit."
        reasonStr NotATheorem   = "Not a theorem."

printError :: Error -> UI ()
printError (AxNameClash nm) =
  printStrLn ("Axiom '" ++ nm ++ "' already in scope. Abort.")
printError (ThrmNameClash nm) =
  printStrLn ("Theorem '" ++ nm ++ "' already in scope. Abort.")
printError (AxNotInScope nm) =
  printStrLn ("Axiom '" ++ nm ++ "' not in scope. Abort.")
printError (ThrmNotInScope nm) =
  printStrLn ("Theorem '" ++ nm ++ "' not in scope. Abort.")

parseFile :: String -> Either ParseError [CLICommand]
parseFile =
  mapM (parseString (padded clicommand)) . filter (not . null . trim) . lines
  where
    padded :: Parser a -> Parser a
    padded p = spaces *> p <* spaces
    isSpace = (== ' ')
    trim = L.dropWhileEnd isSpace . dropWhile isSpace

loadFile :: FilePath -> UI ()
loadFile path =
  readFile path >>= either (printStrLn . show) (mapM_ execComm) . parseFile

initialState :: AppState
initialState = AppState mempty mempty cfg
  where cfg = SearchConfig { _cfgSearchLimit = 2000
                           , _cfgFoundListLen = 3
                           }

execComm :: CLICommand -> UI ()
execComm (AddAxiom nm ax) =
  tryInsert _AxEnv nm ax >>=
    maybe (pure ()) (confirmReplace "Axiom" nm)
execComm (ChangeAxiom nm ax) = changeAxiom nm ax
execComm (RemoveAxioms axs) = removeAll _AxEnv axs
execComm (AddTheorem nm q) = processError $ do
  qr <- query q
  lift $ do
    processQueryResult qr
    case qr of
      Success (_ ::: sequent) ->
        saveTheorem nm q sequent >>= maybe (pure ()) (confirmReplace "Theorem" nm)
      _ -> pure ()
execComm (RemoveTheorems thms) = removeAll _ThrmEnv thms
execComm (RefreshTheorem tm) = processError $
  refreshTheorem tm >>= maybe (throwError (ThrmNotInScope tm)) (lift . processQueryResult)
execComm (Query q) = processError (query q >>= lift . processQueryResult)
execComm (LoadFile p) = loadFile p
execComm (OpenFile p) = execComm Clear >> loadFile p
execComm (SaveToFile p) = do
  (axs, tms) <- (,) <$> use axEnv <*> use tmEnv
  let axComms = fmap (uncurry exportAxiom) (M.toList axs)
      tmComms = fmap (uncurry exportTheorem . second fst) (M.toList tms)
  writeFile p $
    concat . (++ ["\n"]) . L.intersperse "\n" $ axComms ++ tmComms
execComm ListAxioms = printAxioms
execComm ListTheorems = printTheorems
execComm Clear = put initialState
execComm (SetSearchLimit l) = searchConfig.cfgSearchLimit .= l
execComm Help =
  mapM_ printStrLn $
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
