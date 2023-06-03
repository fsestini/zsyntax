{-# LANGUAGE TupleSections, LambdaCase #-}

module Main where

import Control.Monad (forM_)
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Free (foldFree)
import Test.Hspec
import Zsyntax (FailureReason)
import Zsyntax.UI.Core hiding (readFile)
import Zsyntax.CLI.Command (CLICommand(..))
import Zsyntax.CLI.Execution (QueryResult(..))
import Zsyntax.CLI.Structures (Error)

type MockApp a = ExceptT (Either Error FailureReason) (State AppState) a

main :: IO ()
main = do
  xs <- traverse (\fp -> (fp,) <$> readFile ("examples/" ++ fp)) examples
  hspec $ do
    describe "example files" $
      forM_ xs $ \(fp, s) ->
        it ("checks " ++ fp) (checkFile s `shouldBe` True)

mockNatTrans :: UIF x -> MockApp x
mockNatTrans = \case
  (PrintStr s x)     -> pure x
  (GetStr f)         -> pure (f "")
  (Get f)            -> f <$> get
  (Put s x)          -> put s >> pure x
  (ProcessError e x) -> throwError (Left e)
  (ProcessQueryResult r x) -> case r of
    Success _ -> pure x
    Failure e _ -> throwError (Right e)
  (ReadFile fp f)    -> pure (f "")
  (WriteFile fp s x) -> pure x

foldUIMock :: UI a -> MockApp a
foldUIMock = foldFree mockNatTrans . unUI

checkSuccess :: MockApp () -> Bool
checkSuccess = isRight . flip evalState initialState . runExceptT
  where isRight = either (const False) (const True)

checkFile :: String -> Bool
checkFile s =
  either
   (const False)
   (checkSuccess . foldUIMock . mapM_ execComm) (parseFile s)

examples :: [FilePath]
examples =
  [ "feedforwardloop"
  , "glucose-example"
  , "glycolytic"
  , "melanoma"
  , "regulatoryloop"
  , "bool2"
  ]
