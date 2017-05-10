module Main where

import Command
import System.IO
import Control.Monad.Trans.State

main :: IO ()
main = do
  putStrLn "Theorem name:"
  putStr "> "
  hFlush stdout
  name <- getLine
  putStrLn "Start aggregate:"
  putStr "> "
  hFlush stdout
  q1 <- getLine
  putStrLn "End aggregate:"
  putStr "> "
  hFlush stdout
  q2 <- getLine
  foldFree toIO $ execFromState (Query (TN name) q1 q2) mempty
  main

toIO :: UIF a -> IO a
toIO (UILog str x) = (putStrLn $ "log: " ++ str) >> return x
toIO (UILoadFile _ _) = error "not yet supported"
