module Zsyntax.CLI.Command where

import Data.Foldable
import Text.Parsec.Char
import Text.Parsec.Prim (unexpected)
import Text.Parsec hiding (State, token)
import Text.Parsec.String

-- import Text.Parsec
-- import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Data.Functor.Identity
import Control.Monad
-- import Core.LinearContext
import Data.List.NonEmpty (NonEmpty(..))
import Data.List (intersperse, intercalate)
import Data.MultiSet (fromList)

import Zsyntax.ReactionList
import Zsyntax.Formula
import Zsyntax.CLI.Structures

--------------------------------------------------------------------------------
-- Command parsing

{-| Definition of the commands that are supported by the Zsyntax command line
  interface -} 
data CLICommand
  = AddAxiom Name AxRepr
  | ChangeAxiom Name AxRepr
  | RemoveAxioms [Name]
  | AddTheorem Name QueriedSeq
  | RefreshTheorem Name
  | RemoveTheorems [Name]
  | Query QueriedSeq
  | LoadFile FilePath
  -- ^ Loading a file executes all commands in it, so that their effects act on
  -- the state of the system at the moment the file is loaded.
  | OpenFile FilePath
  -- ^ Opening a file executes all commands in it, after having reset the system
  -- to an initial, empty state.
  | SaveToFile FilePath
  | ListAxioms
  | ListTheorems
  | Help
  | Clear
  | SetSearchLimit Int
  -- ^ Clears the system, bringing it to an initial state.

--------------------------------------------------------------------------------
-- Parsing bioformulas

lexer :: Token.GenTokenParser String u Identity
lexer = Token.makeTokenParser languageDef
  where
    languageDef =
      emptyDef { Token.identStart      = letter
               , Token.identLetter     = alphaNum
               , Token.reservedOpNames = [ "<>", "->", "*", ",", "." ]
               }

bioOperators :: [[Operator Char st (BioFormula a)]]
bioOperators = [[Infix (Token.reservedOp lexer "<>" >> return BioInter) AssocLeft]]

bioExpr, bioTerm :: Parser (BioFormula String)
bioExpr = buildExpressionParser bioOperators bioTerm
bioTerm = Token.parens lexer bioExpr <|> fmap BioAtom (Token.identifier lexer)

-- parseBioAggregate :: String -> Either String [BioFormula String]
-- parseBioAggregate = bimap show id . parse (white *> sepBy bioExpr comma <* eof) ""
--   where comma = Token.comma lexer
--         white = Token.whiteSpace lexer

-- parseBioAggregate1 :: String -> Either String (NonEmpty (BioFormula String))
-- parseBioAggregate1 str =
--   case parse (white *> sepBy1 bioExpr comma <* eof) "" str of
--     Left err -> Left (show err)
--     Right [] -> Left "invalid empty aggregate"
--     Right (x:xs) -> Right (x :| xs)
--   where comma = Token.comma lexer
--         white = Token.whiteSpace lexer

--------------------------------------------------------------------------------

parseString :: Parser a -> String -> Either ParseError a
parseString p = parse p ""

sepBy1' :: Parser a -> Parser b -> Parser (NonEmpty a)
sepBy1' p sep = do
  (x : xs) <- sepBy1 p sep
  pure (x :| xs)

name :: Parser Name
name = many1 alphaNum

pAggregate :: Parser [BioFormula BioAtom]
pAggregate = sepBy (bioExpr <* spaces) (comma <* spaces)

aggregate1' :: Parser (NonEmpty (BioFormula BioAtom))
aggregate1' =
  sepBy1 (bioExpr <* spaces) (comma <* spaces) >>= \case
    [] -> unexpected "invalid empty aggregate"
    (x:xs) -> return (x :| xs)

parenAggr :: Parser (NonEmpty (BioFormula BioAtom))
parenAggr = parens (token aggregate1')

ctrlCtxt :: Parser (CtrlSetCtxt (BioFormula BioAtom))
ctrlCtxt =  try (string "regular" >> spaces >> fmap (CSC Regular) neCtxt)
        <|> (string "super" >> spaces >> fmap (CSC SupersetClosed) neCtxt)
  where neCtxt = fromList . toList  <$> aggregate1' -- fromNEList <$> aggregate1'

ctrlSet :: Parser (CtrlSet (BioFormula BioAtom))
ctrlSet = parens . token $
  fromCSCtxts <$> many (parens (token ctrlCtxt) <* spaces)

-- str axiom name (aggr...) (aggr...) unless ((regular ...) (super ...) ...)
pAxiom :: String -> Parser CLICommand
pAxiom str = string str >> token (string "axiom") >> do
  axName <- token name
  fromAggr <- token parenAggr
  toAggr <- token parenAggr
  _ <- token (string "unless")
  ctrlset <- token ctrlSet
  pure (AddAxiom axName (AR fromAggr ctrlset toAggr))

queryAxioms :: AxMode -> Parser QueryAxioms
queryAxioms m = try allParser <|> try someParser
  where
    axiomList = sepBy (name <* spaces) (comma <* spaces)
    allParser =
      string "all" >> spaces >> string "axioms" >> return (QA AllOfEm m)
    someParser =
      string "axioms" >> spaces >>
      (flip QA m . Some <$> parens (token axiomList))
  
-- query name (aggr...) (aggr...) [refine] with axioms (...)
queryTheorem :: Parser CLICommand
queryTheorem =
  string "query" >> do
    maybeName <- fmap Just (try (token name)) <|> pure Nothing
    fromAggr <- token (parens (token pAggregate))
    toAggr <- token parenAggr
    m <- token queryAxMode
    _ <- token (string "with")
    qAxs <- token (queryAxioms m)
    let q = QS qAxs fromAggr toAggr
    (pure . maybe (Query q) (flip AddTheorem q)) maybeName
  where queryAxMode = try (string "refine" >> pure Refine) <|> pure Normal

url :: Parser FilePath
url = many1 (noneOf [' '])

btwSpaces :: [String] -> Parser ()
btwSpaces = foldr1 (>>) . intersperse spaces . fmap ((>> return ()) . string)

pLoadFile, pOpenFile, pSaveToFile, pRemoveAx, pRemoveThrm,
  pSetSearchLimit, pRefreshTheorem :: Parser CLICommand
pLoadFile = string "load file" >> spaces >> LoadFile <$> url
pOpenFile = string "open file" >> spaces >> OpenFile <$> url
pSaveToFile = btwSpaces ["save", "to", "file"] >> SaveToFile <$> token url
pRemoveAx =
  btwSpaces ["remove", "axiom"] >> RemoveAxioms <$> fmap pure (token name)
pRemoveThrm =
  btwSpaces ["remove", "theorem"] >> RemoveTheorems <$> fmap pure (token name)
pSetSearchLimit = do
  btwSpaces ["set", "search", "limit"]
  SetSearchLimit . read <$> token (many1 digit)
pRefreshTheorem = string "refresh" >> RefreshTheorem <$> token name

clicommand :: Parser CLICommand
clicommand = commands <?> "a command name"
  where
    commands = msum (fmap try
      [ pAxiom "add"
      , pAxiom "change"
      , pRemoveAx
      , pRemoveThrm
      , pRefreshTheorem
      , queryTheorem
      , pLoadFile
      , pOpenFile
      , pSaveToFile
      , btwSpaces ["list", "axioms"] >> pure ListAxioms
      , btwSpaces ["list", "theorems"] >> pure ListTheorems
      , token (string "help") >> pure Help
      , token (string "clear") >> pure Clear
      , pSetSearchLimit
      ])

comma :: Parser Char
comma = char ','

parens :: Parser a -> Parser a
parens p = char '(' *> p <* char ')'

token :: Parser a -> Parser a
token p = spaces >> p

--------------------------------------------------------------------------------
-- Export

exportAggregate :: Foldable f => f (BioFormula BioAtom) -> String
exportAggregate = join . intersperse "," . fmap exportBioFormula . toList

exportAxiom :: Name -> AxRepr -> String
exportAxiom nm (AR fromAggr cty toAggr) = mconcat
  [ "add axiom ", nm, " (", exportAggregate fromAggr, ") ("
  , exportAggregate toAggr, ") unless (", exportCtrl cty, ")" ]

exportBioFormula :: BioFormula BioAtom -> String
exportBioFormula (BioAtom x) = x -- pretty x
exportBioFormula (BioInter x y) =
  "(" ++ exportBioFormula x ++ " <> " ++ exportBioFormula y ++ ")"

exportCtrl :: CtrlSet (BioFormula BioAtom) -> String
exportCtrl =
  concatMap (\s -> "(" ++ s ++ ")") . fmap exportCtrlCtxt . toCtxtList

prettys :: Foldable f => (a -> String) -> f a -> String
prettys p = intercalate "," . fmap p . toList

exportCtrlCtxt :: CtrlSetCtxt (BioFormula BioAtom) -> String
exportCtrlCtxt (CSC Regular ctxt) = "regular " ++ prettys (ppBioFormula id) list
  where
    list :: [BioFormula BioAtom]
    list = toList ctxt
exportCtrlCtxt (CSC SupersetClosed ctxt) = "super " ++ prettys (ppBioFormula id) list
  where
    list :: [BioFormula BioAtom]
    list = toList ctxt

exportTheorem :: Name -> QueriedSeq -> String
exportTheorem nm (QS axs fromAggr toAggr) =
  "query " ++ nm ++ " (" ++
  exportAggregate fromAggr ++ ") (" ++ exportAggregate toAggr ++ ")" ++
  qMode ++ " with " ++ qAxs
  where
    qMode =
      case _axMode axs of
        Refine -> " refine"
        Normal -> ""
    qAxs =
      case _requiredAxs axs of
        AllOfEm -> "all axioms"
        Some list -> "axioms (" ++ prettys id list ++ ")"
