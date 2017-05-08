{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module AppMonad (loopIO) where

import Control.Monad.Trans.State.Strict
import qualified Data.Map as M
import SFormula
import Command
import Parser
import Control.Monad.IO.Class
import RelFormula
import Checking
import Text.Parsec
import Data.Bifunctor
import Control.Monad.Trans
import Control.Monad.IO.Class
import System.IO
import Data.Bifunctor
import Control.Monad.Morph
import Control.Monad.Free
import qualified Data.Map as M

import Command

type App a = StateT (Env, ThrmEnv) IO a

toIO :: UIF a -> IO a
toIO (UILog str x) = (putStrLn $ "log: " ++ str) >> return x
toIO (UILoadFile path x) = readFile path >>= return . x

hoistApp :: StateT (Env, ThrmEnv) (Free UIF) a -> App a
hoistApp = hoist (foldFree toIO)

printAxiom :: (String, SAxiom SimpleElemBase SimpleCtrlSet String) -> String
printAxiom (name, ax) = name ++ " : " ++ (show ax)

printAxioms :: App ()
printAxioms = do
  (env, _) <- get
  let list = M.toList env
  mapM_ (liftIO . putStrLn) . map printAxiom $ list
  liftIO . putStrLn $ (show . length $ list) ++ " axioms in total."

printTheorems :: App ()
printTheorems = do
  (_, thrms) <- get
  let list = M.toList thrms
  mapM_ (liftIO . putStrLn) .
    map ((\(x, y) -> x ++ " : " ++ y) . bimap show show) $
    list
  liftIO . putStrLn $ (show . length $ list) ++ " theorems in total."

loop :: App a
loop = do
  liftIO $ putStr "> " >> hFlush stdout
  line <- liftIO getLine
  case parseCommand line of
    Left err ->
      case line of
        "list axioms" -> printAxioms
        "list theorems" -> printTheorems
        "?" -> liftIO $ putStrLn "not yet supported"
        _ -> liftIO $ putStrLn "error: unrecognized command"
    Right c -> hoistApp $ execCommand c
  loop

loopIO :: IO ()
loopIO = fst <$> runStateT loop mempty
