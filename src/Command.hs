{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}

module Command
  ( Command(..)
  , Env
  , ThrmEnv
  , UIF(..)
  , UI
  , ThrmName(..)
  , CSString(..)
  , AxiomsString(..)
  , QueriedSeq(..)
  , foldFree
  , execCommand
  , parseCommand
  -- , execFromState
  ) where

import Text.Parsec.Char
import Text.Parsec hiding (State, token)
import Text.Parsec.String

import qualified Data.List.NonEmpty as NE
import Data.List.Split (splitOn)
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
import Control.Arrow ((>>>))
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


newtype ThrmName = TN String deriving (Eq, Ord)
newtype CSString = CSS String deriving (Eq, Ord, Show)
newtype AxiomsString = AS String deriving (Eq, Ord, Show)

data QueriedSeq = QS
  { axStr :: AxiomsString
  , fromStr :: String
  , toStr :: String
  } deriving (Eq, Ord)

instance Show QueriedSeq where
  show (QS (AS ax) fr to) = ax ++ " ; " ++ fr ++ " ===> " ++ to

instance Show ThrmName where
  show (TN name) = name

data Command = AddAxiom ThrmName CSString String String
             | ChangeAxiom ThrmName CSString String String
             | Query ThrmName QueriedSeq
             | LoadFile FilePath
             | SaveToFile FilePath
             deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Free monad interface

data UIF next
  = UILog String next
  | UILoadFile FilePath (String -> next)
  | UISaveFile FilePath String next
  deriving (Functor)

type UI a = Free UIF a

logUI :: String -> Free UIF ()
logUI str = liftF (UILog str ())

uiLoadFile :: FilePath -> Free UIF String
uiLoadFile path = liftF (UILoadFile path id)

uiSaveFile :: FilePath -> String -> Free UIF ()
uiSaveFile path content = liftF (UISaveFile path content ())

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

splitTrim :: String -> [String]
splitTrim str = filter (not . null) $ map trim $ splitOn "," (trim str)

parseCtrlSet :: String -> Either String (SimpleCtrlSet String)
parseCtrlSet str = fmap ctrlFromFoldable . parseBioAggregate $ str

boh
  :: (String -> Either ParseError (SFormula eb SimpleCtrlSet String))
  -> NE.NonEmpty String
  -> Either ParseError (SFormula eb SimpleCtrlSet String)
boh f l = fmap (foldr1 sConj) $ forM l f

-- execFromState :: Command -> Env -> Free UIF Env
-- execFromState c = fmap snd . runStateT (execCommand c)

parseAxiomStr :: Env
              -> String
              -> Either String (SAxiom SimpleElemBase SimpleCtrlSet String)
parseAxiomStr env str =
  case M.lookup str env of
    Nothing -> Left $ "axiom '" ++ str ++ "' not in scope"
    Just ax -> Right ax



--------------------------------------------------------------------------------
-- Single command execution

parseAxiom :: String
           -> String
           -> CSString
           -> Either String (SAxiom eb SimpleCtrlSet String)
parseAxiom strFrom strTo (CSS ctrlset) = do
  ctrl <- bimap (("ctrl error" ++) . show) id $ parseCtrlSet ctrlset
  fromAggr <- bimap ("from error" ++) id $ parseBioAggregate1 strFrom
  toAggr <- bimap ("to error" ++) id $ parseBioAggregate1 strTo
  return $
    sAx
      (foldr1 sConj . fmap sAtom $ fromAggr)
      (foldr1 sConj . fmap sAtom $ toAggr)
      ctrl

type Env = M.Map String (SAxiom SimpleElemBase SimpleCtrlSet String)
type ThrmEnv = M.Map ThrmName QueriedSeq

addAxiom :: Env -> ThrmName -> CSString -> String -> String -> Free UIF Env
addAxiom env (TN name) ctrlset strFrom strTo =
  case (parseAxiom strFrom strTo ctrlset) of
    Left err -> (logUI $ "parseAxiom error: " ++ (show err)) >> return env
    Right axiom -> return $ M.insert name axiom env

query :: Env -> ThrmEnv -> ThrmName -> QueriedSeq -> Free UIF (ThrmEnv)
query env thrms nm q =
  case (queryToSequent env q) of
    Left err -> (logUI $ "parse error: " ++ err) >> return thrms
    Right actualSequent -> do
      case runSearch actualSequent of
        Nothing -> (logUI $ "Not provable.") >> return thrms
        Just (DT dt _ _) ->
          (logUI $ "Provable with " ++ (show (length impls)) ++ " transitions.") >>
          forM_ impls (logUI . show) >>
          return (M.insert nm q thrms)
          where impls = transitions dt

queryToSequent :: Env -> QueriedSeq -> Either String MySeq
queryToSequent env (QS (AS axioms) q1 q2) = do
  lctxt <- fmap (fmap sAtom) $ parseBioAggregate1 q1
  concl <- fmap (foldr1 sConj . fmap sAtom) (parseBioAggregate1 q2)
  axioms <- mapM (parseAxiomStr env) (splitTrim axioms)
  return $
    SQ (fromFoldable axioms) (fromFoldable (lctxt :: NE.NonEmpty MySF)) concl

changeAxiom
  :: Env
  -> ThrmName
  -> CSString
  -> String
  -> String
  -> ThrmEnv
  -> Free UIF (Env, ThrmEnv)
changeAxiom axEnv (TN axName) axCS axFrom axTo thrms =
  case newEnvE of
    Left err -> undefined
    Right newEnv ->
      fmap ((,) newEnv) $ foldr (<=<) return (maps newEnv) $ mempty
  where
    mmm env (x, y) = toMap x y (checkThrm env y)
    maps env = map (mmm env) (M.toList thrms)
    newEnvE = do
      ax <- parseAxiom axFrom axTo axCS
      return $ M.insert axName ax axEnv
    checkThrm env =
      queryToSequent env >>>
      pe >>>
      fmap runSearch >>>
      fmap (efm "unsatisfied biological constraints") >>>
      join >>> (>> return ())
    toMap (TN name) _ (Left err) x =
      (logUI $ "Theorem '" ++ name ++ "' is not provable anymore: " ++ err) >>
      return x
    toMap (TN name) s (Right ()) x =
      (logUI $ "Theorem '" ++ name ++ "' is still provable.") >>
      return (M.insert (TN name) s x)

loadFile :: FilePath -> StateT (Env, ThrmEnv) (Free UIF) ()
loadFile path = do
  contents <- lift $ uiLoadFile path
  let commandsE = mapM (parseCommand) (lines contents)
  case commandsE of
    Left err -> lift . logUI $ "error parsing the file: " ++ (show err)
    Right commands -> mapM_ execCommand commands

--------------------------------------------------------------------------------
-- Generic command execution

execCommand
  :: Command -> StateT (Env, ThrmEnv) (Free UIF) ()
execCommand (AddAxiom name ctrlset strFrom strTo) = do
  (env, thrms) <- get
  newEnv <- lift $ addAxiom env name ctrlset strFrom strTo
  put (newEnv, thrms)
execCommand (ChangeAxiom name ctrlset strFrom strTo) = do
  (env, thrms) <- get
  (newEnv, newThrms) <- lift $ changeAxiom env name ctrlset strFrom strTo thrms
  put (newEnv, newThrms)
execCommand (Query name q) = do
  (env, thrms) <- get
  newThrms <- lift $ query env thrms name q
  put (env, newThrms)
execCommand (LoadFile path) = loadFile path
execCommand (SaveToFile _) = lift $ logUI "saving to files not yet supported"

--------------------------------------------------------------------------------

runSearch :: MySeq -> Maybe MyDTSeq
runSearch actualSequent = runIdentity $ mySearch initS initR neutral
  where
    neutral = fst $ runState (unLM $ myNeutralize actualSequent) 0
    (initS, initR) = myInitialSequentsAndRules neutral

type BioAtoms = String
type Labels = Int

type MySeq = Sequent SimpleElemBase SimpleCtrlSet BioAtoms
type MyNSeq = NeutralSequent SimpleElemBase SimpleCtrlSet BioAtoms Labels
type MyDTSeq = DTSequent (SimpleDerTerm BioAtoms) SimpleElemBase SimpleCtrlSet BioAtoms Labels
type MyUnaryRule = UnaryRule (SimpleDerTerm BioAtoms) SimpleElemBase SimpleCtrlSet BioAtoms Labels

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

--------------------------------------------------------------------------------
-- Command parsing

parseCommand :: String -> Either ParseError Command
parseCommand = parse command ""

token :: Parser a -> Parser a
token p = spaces >> p

thrmName :: Parser ThrmName
thrmName = TN <$> many1 alphaNum

aggregate1 :: Parser String
aggregate1 =
  join . intersperse "," <$>
  a1

aggregate :: Parser String
aggregate =
  join . intersperse "," <$>
  a

a1 = sepBy1 (try (token (many1 (noneOf [',', '(', ')'])))) (try comma)
a = sepBy (try (token (many1 (noneOf [',', '(', ')'])))) (try comma)

bboh = comma >> token (many1 alphaNum)
mah = token (many1 alphaNum) >> bboh >> (token (char ')'))

ddd = many (try bboh)

rrr = sepBy (try (token (many1 alphaNum))) (try comma)

-- add axiom name (aggr...) (aggr...) unless (aggr...)
parseAddAxiom :: Parser Command
parseAddAxiom = token (string "add") >> token (string "axiom") >> do
  name <- token thrmName
  from <- parens (aggregate1)
  spaces
  to <- parens (aggregate1)
  token (string "unless")
  ctrlset <- parens (aggregate)
  return $ AddAxiom name (CSS ctrlset) from to

parseEditAxiom :: Parser Command
parseEditAxiom = token (string "change") >> token (string "axiom") >> do
  name <- token thrmName
  from <- parens (aggregate1)
  spaces
  to <- parens (aggregate1)
  token (string "unless")
  ctrlset <- parens (aggregate)
  return $ ChangeAxiom name (CSS ctrlset) from to

-- query name (aggr...) (aggr...) with axioms (...)
parseQuery :: Parser Command
parseQuery =
  token (string "query") >> do
    name <- token thrmName
    from <- parens (aggregate1)
    spaces
    to <- parens (aggregate1)
    token (string "with axioms")
    axioms <- parens (aggregate)
    return $ Query name (QS (AS axioms) from to)

parseLoadFile :: Parser Command
parseLoadFile = token (string "load file") >> LoadFile <$> token (many1 (noneOf [' ']))

parseSaveToFile :: Parser Command
parseSaveToFile =
  token (string "save to file") >> SaveToFile <$> many1 (noneOf [' '])

command :: Parser Command
command =
  parseAddAxiom <|> parseEditAxiom <|> parseQuery <|> parseLoadFile <|>
  parseSaveToFile

comma = token (char ',')
parens :: Parser a -> Parser a
parens p = token (char '(') *> p <* token (char ')')

--------------------------------------------------------------------------------

pe :: Either String a -> Either String a
pe = first ("parse error: " ++)

applyTwo :: (a -> b) -> (a -> c) -> a -> (b, c)
applyTwo f g x = (f x, g x)

efm :: a -> Maybe b -> Either a b
efm x = maybe (Left x) return
