{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE TypeSynonymInstances #-}

module CLI.Command where

import Text.Parsec.Char
import Text.Parsec.Prim (unexpected)
import Text.Parsec hiding (State, token)
import Text.Parsec.String

import Control.Monad.State
import LinearContext
import qualified Data.List.NonEmpty as NE
import Command.Structures
import Checking.ReactLists.RList
import Checking.ReactLists.Sets
import qualified SFormula as S
import LFormula
       (BioFormula(..), SrchFormula, LGoalNSequent, BFormula, decideN,
        decideOF)
import Rules hiding (AxRepr, AR)
import Parser
import Control.Monad (join)
import Data.List (intersperse)
import Data.List.Split (splitOn)
import Data.Char (isSpace)
import Data.List (dropWhileEnd)
import Data.Foldable (toList)
import Data.Bifunctor (bimap)
import Context
import qualified TypeClasses as T
import qualified SimpleDerivationTerm as SDT

newtype Aggregate = Aggr { unAggr :: NE.NonEmpty (BioFormula BioAtoms) }
  deriving (Eq, Ord, Show)

instance T.Pretty Aggregate where
  pretty = T.prettys . unAggr

data AxRepr = AR
  { from :: Aggregate
  , ctrl :: CtrlSet BioAtoms
  , to :: Aggregate
  } deriving (Eq, Ord, Show)

type FrmlRepr = Aggregate

type BioAtoms = String
type CLIElemBase = ElemBase BioAtoms
type CLICtrlSet = CtrlSet BioAtoms
type CLIControlType = RList CLIElemBase CLICtrlSet
-- The particular fully applied type of axioms that are used in the user
-- interface.
type CLIAxiom = S.SAxiom CLIControlType BioAtoms
-- The particular fully applied type of formulas that are used in the user
-- interface.
type CLIFormula = S.SFormula CLIElemBase CLIControlType String

type CLIAxEnv = AxEnv AxRepr CLIAxiom
type CLIThrmEnv = ThrmEnv Aggregate CLIAxiom

type CLIDerTerm = SDT.SimpleDerTerm BioAtoms

newtype CLITransRepr = CTR (S.SFormula () () BioAtoms, S.SFormula () () BioAtoms)

type CLISrchFormula = SrchFormula CLIElemBase CLIControlType BioAtoms Int

instance T.Pretty CLITransRepr where
  pretty (CTR (f1, f2)) = T.pretty f1 ++ " --> " ++ T.pretty f2

type instance DerT CLIAxiom AxRepr FrmlRepr = CLIDerTerm

instance Search CLIAxiom AxRepr FrmlRepr where
  type SrchF CLIAxiom AxRepr FrmlRepr = CLISrchFormula
  fromRNS (RNS _ lc cty concl) =
    maybe NonAxiomatic Axiomatic $ do
      lc <- mapM decideN $ toNEList lc
      to <- decideOF concl
      return $ S.fromBasicNS lc cty to
  queryToGoal axs thrms (QS axlist q1 q2) = do
    axioms <-
      case axlist of
        Some list -> axsFromList axs thrms list
        AllOfEm -> return (fmap snd (legitAxioms axs thrms))
    let lc = fmap S.sAtom . unAggr $ q1
        concl = foldr1 S.sConj . fmap S.sAtom . unAggr $ q2
        sq = S.SQ (fromFoldable axioms) (fromNEList lc) concl
        gns = fst $ runState (unPM . neutralize $ sq) 0
    return gns

instance TransDerTerm CLIDerTerm where
  type TransRepr CLIDerTerm = CLITransRepr
  transitions = fmap CTR . SDT.transitions

--------------------------------------------------------------------------------
-- Auxiliary PickMonad

neutralize
  :: (Num n, Ord n)
  => S.Sequent CLIElemBase CLIControlType BioAtoms
  -> PickM n (LGoalNSequent CLIElemBase CLIControlType BioAtoms n)
neutralize = S.neutralize

newtype PickM n a = PM { unPM :: State n a }
deriving instance Applicative (PickM n)
deriving instance Functor (PickM n)
deriving instance Monad (PickM n)
deriving instance MonadState n (PickM n)
instance Num n => T.PickMonad (PickM n) n where
  pick = do
    i <- get
    put (i + 1)
    return i

instance CommAx AxRepr CLIAxiom where
  reprAx (AR from ctrl to) = do
    return $
      S.sAx
        (foldr1 S.bsConj . fmap S.bsAtom . unAggr $ from)
        (foldr1 S.bsConj . fmap S.bsAtom . unAggr $ to)
        (RL [(mempty, ctrl)])

--------------------------------------------------------------------------------
-- Command parsing

type CLICommand = Command AxRepr FrmlRepr

instance CParse AxRepr FrmlRepr where
  parseCommand = bimap show id . CLI.Command.parseCommand

parseCommand :: String -> Either ParseError CLICommand
parseCommand = parse command ""

thrmName :: Parser ThrmName
thrmName = TN <$> many1 alphaNum

aggregate1' :: Parser (NE.NonEmpty (BioFormula BioAtoms))
aggregate1' = do
  aggr <- sepBy1 (token bioExpr) comma
  case aggr of
    [] -> unexpected "invalid empty context in control set"
    (x:xs) -> return (x NE.:| xs)

neCtxt :: Parser (NonEmptyLinearCtxt (BioFormula BioAtoms))
neCtxt = do
  aggr <- aggregate1'
  let ctxt = fromNEList aggr
  return ctxt

ctrlCtxt :: Parser (CtrlSetCtxt BioAtoms)
ctrlCtxt =  try (token (string "regular") >> fmap Regular neCtxt)
        <|> (token (string "super") >> fmap SupsetClosed neCtxt)

ctrlSet :: Parser (CtrlSet BioAtoms)
ctrlSet = do
  ctxts <- many (try (parens ctrlCtxt))
  return (fromFoldableCtxts ctxts)

-- str axiom name (aggr...) (aggr...) unless ((regular ...) (super ...) ...)
parseAxiom :: String -> Parser CLICommand
parseAxiom str = token (string str) >> token (string "axiom") >> do
  name <- token thrmName
  from <- parens (aggregate1')
  spaces
  to <- parens (aggregate1')
  _ <- token (string "unless")
  ctrlset <- parens ctrlSet
  return $ AddAxiom name (AR (Aggr from) ctrlset (Aggr to))

axiomList :: Parser [ThrmName]
axiomList = sepBy ((spaces *> thrmName <* spaces)) comma

queryAxioms :: Parser QueryAxioms
queryAxioms = try allParser <|> try someParser
  where
    allParser :: Parser QueryAxioms
    allParser = string "all" >> spaces >> string "axioms" >> return AllOfEm
    someParser :: Parser QueryAxioms
    someParser = string "axioms" >> spaces >> (Some <$> parens axiomList)

-- query name (aggr...) (aggr...) with axioms (...)
queryTheorem :: Parser CLICommand
queryTheorem =
  token (string "query") >> do
    maybeName <- fmap Just (try (token thrmName)) <|> return Nothing
    from <- parens (aggregate1')
    spaces
    to <- parens (aggregate1')
    _ <- token (string "with")
    qAxs <- spaces >> queryAxioms
    let q = QS qAxs (Aggr from) (Aggr to)
    case maybeName of
      Just name -> return $ AddTheorem name q
      Nothing -> return $ Query q

parseLoadFile :: Parser CLICommand
parseLoadFile =
  token (string "load file") >> spaces >>
  LoadFile <$> token (many1 (noneOf [' ']))

parseSaveToFile :: Parser CLICommand
parseSaveToFile =
  token (string "save to file") >> spaces >> SaveToFile <$> many1 (noneOf [' '])

parseRemoveAxiom :: Parser CLICommand
parseRemoveAxiom =
  RemoveAxioms . return <$> (token (string "remove axiom") >> (token thrmName))

command :: Parser CLICommand
command =
  parseAxiom "add" <|> parseAxiom "edit" <|> queryTheorem
  <|> parseLoadFile <|> parseSaveToFile <|> parseRemoveAxiom

comma :: Parser Char
comma = token (char ',')

parens :: Parser a -> Parser a
parens p = token (char '(') *> p <* token (char ')')

token :: Parser a -> Parser a
token p = spaces >> p

--------------------------------------------------------------------------------
-- Export

instance CPrint AxRepr FrmlRepr where
  printAx = exportAxiom
  printThrm = exportTheorem

exportAxiom :: ThrmName -> AddedAxiom AxRepr -> String
exportAxiom (TN name) (AAx (AR from cty to)) =
  "add axiom " ++ name ++ " (" ++ T.pretty from ++ ") (" ++ T.pretty to
  ++ ") unless (" ++ exportCtrl cty ++ ")"

ppBioFormula :: BioFormula BioAtoms -> String
ppBioFormula (BioAtom x) = T.pretty x
ppBioFormula (BioInter x y) = ppBioFormula x ++ " <> " ++ ppBioFormula y

exportCtrl :: CtrlSet BioAtoms -> String
exportCtrl =
  concat . fmap (\s -> "(" ++ s ++ ")") . fmap exportCtrlCtxt . toCtxtList

exportCtrlCtxt :: CtrlSetCtxt BioAtoms -> String
exportCtrlCtxt (Regular ctxt) = "regular " ++ T.prettys list
  where
    list :: [BioFormula BioAtoms]
    list = asFoldable toList ctxt
exportCtrlCtxt (SupsetClosed ctxt) = "super " ++ T.prettys list
  where
    list :: [BioFormula BioAtoms]
    list = asFoldable toList ctxt

exportTheorem :: ThrmName -> QueriedSeq FrmlRepr -> String
exportTheorem (TN name) (QS axs from to) =
  "query " ++
  name ++ " (" ++ T.pretty from ++ ") (" ++ T.pretty to ++ ") with " ++ qAxs
  where
    qAxs =
      case axs of
        AllOfEm -> "all axioms"
        Some list -> "axioms (" ++ T.prettys list ++ ")"

--------------------------------------------------------------------------------

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace
