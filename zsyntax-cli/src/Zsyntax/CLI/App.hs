{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Zsyntax.CLI.App (loopIO) where

import Text.Parsec.Char (spaces)
import Data.List (isPrefixOf)
import System.Console.Haskeline
import Control.Monad.State
import System.IO (hFlush, stdout)
import Control.Monad.Free (foldFree)

import Zsyntax.CLI.Utils
import Zsyntax.CLI.Command
import Control.Monad.Catch (MonadThrow, MonadMask, MonadCatch)
import Zsyntax.UI.Core
  (UI(..), UIF(..), AppState(..), printError, printQR, execComm, initialState)

newtype App a = App
  { unApp :: StateT AppState IO a
  } deriving (Functor, Applicative, Monad, MonadState AppState, MonadIO,
              MonadThrow, MonadCatch, MonadMask)

appNatTrans :: UIF x -> App x
appNatTrans = \case
  (PrintStr s x)     -> liftIO (putStr s >> hFlush stdout) >> pure x
  (GetStr f)         -> f <$> liftIO getLine
  (Get f)            -> f <$> get
  (Put s x)          -> put s >> pure x
  (ProcessError e x) -> foldUIApp (printError e) >> pure x
  (ProcessQueryResult r x) -> foldUIApp (printQR r) >> pure x
  (ReadFile fp f)    -> f <$> liftIO (readFile fp)
  (WriteFile fp s x) -> liftIO (writeFile fp s) >> pure x

foldUIApp :: UI a -> App a
foldUIApp = foldFree appNatTrans . unUI

execCommApp :: CLICommand -> App ()
execCommApp = foldUIApp . execComm

loop :: InputT App a
loop = do
  mline <- getInputLine ">>> "
  maybe' mline (pure ()) $ \line ->
    case parseString (spaces *> clicommand <* spaces) line of
      Left err -> outputStrLn (show err)
      Right c -> lift (execCommApp c)
  loop

loopIO :: IO ()
loopIO = fmap (fst . fst) . flip runStateT initialState . unApp . runInputT settings $ loop
  where
    wordList = [ "axiom", "axioms", "list", "query", "theorems", "unless", "clear" ]
    searchFun str = map simpleCompletion $ filter (str `isPrefixOf`) wordList
    settings = Settings (completeWord Nothing " \t" (pure . searchFun)) Nothing True
