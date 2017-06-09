{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module CLI.App (loopIO) where

import Control.Monad.Trans.State.Strict
import qualified Data.Map as M
import SFormula
--import Command
--import Parser
import Control.Monad.IO.Class
import LFormula
--import Checking
import Text.Parsec
import Data.Bifunctor
import Control.Monad.Trans
import Control.Monad.IO.Class
import System.IO
import Data.Bifunctor
import Control.Monad.Morph
import Control.Monad.Free
import qualified Data.Map as M
import Parsing

import TypeClasses (Pretty(..))

import Command.Structures
       (UIF(..), ThrmName(..), FEnv(..), AddedAxiom(..), CParse(..))
import Command.Execution (execCommand)
import CLI.Command

type App a = StateT (CLIAxEnv, CLIThrmEnv) IO a

toIO :: UIF a -> IO a
toIO (UILog str x) = (putStrLn $ "log: " ++ str) >> return x
toIO (UILoadFile path x) = readFile path >>= return . x
toIO (UISaveFile path content x) = writeFile path content >> return x

hoistApp :: StateT (CLIAxEnv, CLIThrmEnv) (Free UIF) a -> App a
hoistApp = hoist (foldFree toIO)

printAxiom :: (ThrmName, AddedAxiom AxRepr) -> String
printAxiom (TN name, (AAx (AR from _ to))) =
  name ++ " : " ++ (pretty from) ++ " -> " ++ (pretty to)

printAxioms :: App ()
printAxioms = do
  (env, _) <- get
  let list = feAsList env
  mapM_ (liftIO . putStrLn) . map (printAxiom . second fst) $ list
  liftIO . putStrLn $ (show . length $ list) ++ " axioms in total."

printTheorems :: App ()
printTheorems = do
  (_, thrms) <- get
  let list = fmap (second fst) . feAsList $ thrms
  mapM_ (liftIO . putStrLn) .
    map ((\(x, y) -> x ++ " : " ++ y) . bimap show pretty) $
    list
  liftIO . putStrLn $ (show . length $ list) ++ " theorems in total."

loop :: App a
loop = do
  liftIO $ putStr "> " >> hFlush stdout
  line <- liftIO getLine
  case (parseString (padded pCommand)) line of
    Left err ->
      case line of
        "list axioms" -> printAxioms
        "list theorems" -> printTheorems
        "?" -> liftIO $ putStrLn "not yet supported"
        _ -> liftIO $ putStrLn "error: unrecognized command"
    Right c -> hoistApp $ execCommand c
  loop

loopIO :: IO ()
loopIO = fst <$> runStateT loop (feEmpty, feEmpty)
