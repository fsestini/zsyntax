{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}

module Command
  ( Command(..)
  , Env
  , UIF(..)
  , UI
  , ThrmName(..)
  , CSString(..)
  , foldFree
  , execCommand
  , execFromState
  ) where

import qualified Data.List.NonEmpty as NE
import Data.List.Split
import Data.List
import Data.Char

import qualified Data.Map as M
import Context
import TypeClasses (PickMonad(..))
import qualified Data.Set as S
import Relation
import SFormula
import Parser
import Control.Monad.IO.Class
import RelFormula
import Checking
import Text.Parsec (ParseError)
import Data.Bifunctor
import Control.Monad.Trans.State.Strict hiding (get, put)
import Control.Monad.State.Class
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Free
import Control.Monad.Trans
import LinearContext
import RelFormula
import Prover
import Frontier
import Context
import DerivationTerm


newtype ThrmName = TN String
newtype CSString = CSS String

data Command = AddAxiom ThrmName CSString String
             | Query ThrmName String String
             | LoadFile FilePath

--------------------------------------------------------------------------------
-- Free monad interface

data UIF next
  = UILog String
          next
  | UILoadFile FilePath
               (String -> next)
  deriving (Functor)

type UI a = Free UIF a

logUI :: String -> Free UIF ()
logUI str = liftF (UILog str ())

uiLoadFile :: FilePath -> Free UIF String
uiLoadFile path = liftF (UILoadFile path id)

asd :: Free UIF ()
asd = do
  logUI "asd"
  logUI "lol"
  content <- uiLoadFile "path"
  logUI "lll"
  logUI content

ioNT :: UIF a -> IO a
ioNT (UILog str x) = putStrLn str >> return x
ioNT (UILoadFile path k) = return $ k (show path)

toIO :: Free UIF () -> IO ()
toIO = foldFree ioNT

--------------------------------------------------------------------------------
-- Command execution

trim = dropWhileEnd isSpace . dropWhile isSpace

checkSplit :: String -> Either String (NE.NonEmpty String)
checkSplit str =
  case splitOn "," (trim str) of
    [] -> Left "cannot have empty aggregate"
    (x:xs) -> Right $ x NE.:| xs

parseCtrlSet :: String -> Either ParseError (SimpleCtrlSet String)
parseCtrlSet = undefined

boh
  :: (String -> Either ParseError (SFormula eb SimpleCtrlSet String))
  -> NE.NonEmpty String
  -> Either ParseError (SFormula eb SimpleCtrlSet String)
boh f l = fmap (foldr1 sConj) $ forM l f

type Env = (M.Map String (SAxiom SimpleElemBase SimpleCtrlSet String))

execFromState :: Command -> Env -> Free UIF Env
execFromState c = fmap snd . runStateT (execCommand c)

execCommand
  :: Command -> StateT Env (Free UIF) ()
execCommand (AddAxiom (TN name) (CSS ctrlset) str) = do
  state <- get
  let ax =
        (bimap show id $ parseCtrlSet ctrlset) >>=
        flip (parseSAxiom (fmap sAxiomIsSFormula state)) str
  case ax of
    Left err -> lift . logUI $ "parse error: " ++ (show err)
    Right axiom -> do
      let newState = M.insert name axiom state
      put newState
execCommand (Query (TN name) q1 q2) = do
  state <- get
  let mappedState = fmap sAxiomIsSFormula state
  let sequent = do
        let split1 = splitOn "," q1
        split2 <- checkSplit q2
        lctxt <- bimap show id $ mapM (parseSFormula mappedState) split1
        concl <- bimap show id $ boh (parseSFormula mappedState) split2
        return $ SQ (fromFoldable (M.elems state)) (fromFoldable lctxt) concl
  case sequent of
    Left err -> lift . logUI $ "parse error: " ++ err
    Right actualSequent -> do
      case runSearch actualSequent of
        Nothing -> lift . logUI $ "Not provable."
        Just (DT dt _) ->
          (lift . logUI $
           "Provable with " ++ (show (length impls)) ++ " transitions.") >>
          forM_ impls (lift . logUI . show)
          where impls :: [MySF]
                impls =
                  fmap (SF . OLF . Impl' . fmap (const ())) $ getTransitions dt
execCommand (LoadFile path) = do
  content <- lift . uiLoadFile $ path
  let commands = map parseCommand (lines content)
  forM_ commands execCommand

runSearch :: MySeq -> Maybe MyDTSeq
runSearch actualSequent = runIdentity $ mySearch initS initR neutral
  where
    neutral = fst $ runState (unLM $ myNeutralize actualSequent) 0
    (initS, initR) = myInitialSequentsAndRules neutral

type BioAtoms = String
type Labels = Int

type MySeq = Sequent SimpleElemBase SimpleCtrlSet BioAtoms
type MyNSeq = NeutralSequent SimpleElemBase SimpleCtrlSet BioAtoms Labels
type MyDTSeq =
  DTSequent
    (SimpleDerTerm SimpleElemBase SimpleCtrlSet BioAtoms Labels)
    SimpleElemBase SimpleCtrlSet BioAtoms Labels
type MyUnaryRule =
  UnaryRule
    (SimpleDerTerm SimpleElemBase SimpleCtrlSet BioAtoms Labels)
      SimpleElemBase SimpleCtrlSet BioAtoms Labels

myInitialSequentsAndRules :: MyGSeq -> (S.Set MyDTSeq, [MyUnaryRule])
myInitialSequentsAndRules = initialSequentsAndRules

newtype LabelMonad a =
  LM {unLM :: (State Int a)}
  deriving (Functor, Applicative, Monad, MonadState Int)

instance PickMonad LabelMonad Int where
  pick = do
    i <- get
    put (i + 1)
    return i

mySearch :: S.Set MyDTSeq -> [MyUnaryRule] -> MyGSeq -> Identity (Maybe MyDTSeq)
mySearch = proverSearch

type MyGSeq = GoalNeutralSequent SimpleElemBase SimpleCtrlSet BioAtoms Labels

myNeutralize :: MySeq -> LabelMonad MyGSeq
myNeutralize = flip neutralize Nothing

type MySF = SFormula SimpleElemBase SimpleCtrlSet BioAtoms


-- loop :: IO ()
-- loop = do
--   putStrLn "Start aggregate:"
--   putStr "> "
--   hFlush stdout
--   query1 <- getLine
--   putStrLn "End aggregate:"
--   putStr "> "
--   hFlush stdout
--   query2 <- getLine
--   case checkSplit query2 of
--     Nothing -> undefined
--     Just splitQ2 -> do
--       let sequent = do
--             q1 <- mapM (parseSFormula mempty) (splitOn "," query1)
--             q2 <- boh (parseSFormula mempty) splitQ2
--             return $ (SQ mempty (fromFoldable (q1 :: [MySF])) q2 :: MySeq)
--       case sequent of
--         Left err -> putStrLn $ "parse error: " ++ (show err)
--         Right res -> do
--           let neutral = fst $ runState (unLM $ myNeutralize res) 0
--               (initS, initR) = myInitialSequentsAndRules neutral
--               (Identity sres) = mySearch initS initR neutral
--           case sres of
--             Nothing -> putStrLn "Not provable." >> loop
--             Just (DT dt _) ->
--               (putStrLn $
--                "Provable with " ++ (show (length impls)) ++ " transitions.") >>
--               forM_ impls (putStrLn . show) >>
--               loop
--               where impls :: [MySF]
--                     impls =
--                       fmap (SF . OLF . Impl' . fmap (const ())) $
--                       getTransitions dt
--             -- putStrLn (show (getTransitions dt)) >> loop
--   -- case parseSFormula mempty query of
--   --   Left err -> putStrLn $ "parse error: " ++ (show err)
--   --   Right res -> undefined


--------------------------------------------------------------------------------
-- Command parsing

-- TODO

parseCommand :: String -> Command
parseCommand = undefined
