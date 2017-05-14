{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Parser (parseBioAggregate, parseBioAggregate1) where

import System.IO
import qualified Data.List.NonEmpty as NE
import Control.Monad
import Text.Parsec
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import SFormula
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Control.Monad.Reader
import Control.Monad.Identity
import Data.Bifunctor

type ParseAtom = BioFormula String
type ParseFormula = SFormula U U String

languageDef =
  emptyDef { Token.identStart      = letter
           , Token.identLetter     = alphaNum
           , Token.reservedOpNames = [ "<>", "->", "*", ",", "." ]
           }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reservedOp = Token.reservedOp lexer
parens = Token.parens lexer
comma = Token.comma lexer
white = Token.whiteSpace lexer

bioOperators = [[Infix (reservedOp "<>" >> return BioInter) AssocLeft]]
logicOperators =
  [ [Infix (reservedOp "*" >> return sConj) AssocLeft]
  , [Infix (reservedOp "->" >> return (flip (flip sImpl U) U)) AssocRight]
  ]

bioExpr :: Parser ParseAtom
bioExpr = buildExpressionParser bioOperators bioTerm



bioTerm :: Parser ParseAtom
bioTerm =  parens bioExpr
       <|> fmap BioAtom identifier

logicExpr :: Parser ParseFormula
logicExpr = buildExpressionParser logicOperators logicTerm

logicTerm :: Parser ParseFormula
logicTerm =  parens logicExpr
         <|> fmap sAtom bioExpr

parseString :: String -> Either ParseError ParseFormula
parseString str = parse (white >> logicExpr) "" str

toSAtom :: M.Map String (SFormula eb cs String)
        -> ParseAtom
        -> SFormula eb cs String
toSAtom m a@(BioAtom x) = fromMaybe (sAtom a) (M.lookup x m)
toSAtom _ a@(BioInter _ _) = sAtom a

parseBioFormula :: String -> Either ParseError (BioFormula String)
parseBioFormula = parse (white >> bioExpr) ""

toSFormula
  :: (ElemBase eb String, ControlSet cs String)
  => M.Map String (SFormula eb cs String)
  -> ParseFormula
  -> SFormula eb cs String
toSFormula m (SF (OLF (Atom a))) = toSAtom m a
toSFormula m (SF (OLF (Conj f1 f2 _))) =
  sConj (toSFormula m (SF (OLF f1))) (toSFormula m (SF (OLF f2)))
toSFormula m (SF (OLF (Impl f1 _ _ f2 _))) =
  (sImpl (toSFormula m (SF (OLF f1))) mempty mempty (toSFormula m (SF (OLF f2))))

-- parseSFormula
--   :: (ElemBase eb String, ControlSet cs String)
--   => M.Map String (SFormula eb cs String)
--   -> String
--   -> Either ParseError (SFormula eb cs String)
-- parseSFormula m = (return . toSFormula m) <=< parseString

-- parseSAxiom
--   :: (ElemBase eb String, ControlSet cs String)
--   => M.Map String (SFormula eb cs String)
--   -> cs String
--   -> String
--   -> Either String (SAxiom eb cs String)
-- parseSAxiom m cs str = do
--   res <- bimap show id (parseString str)
--   case res of
--     (SF (OLF (Impl a _ _ b _))) ->
--       return $ sAx (toSFormula m (SF (OLF a))) (toSFormula m (SF (OLF b))) cs
--     _ -> fail "axioms must be implication formulas"

parseBioAggregate :: String -> Either String [BioFormula String]
parseBioAggregate = bimap show id . parse (white *> sepBy bioExpr comma <* eof) ""

parseBioAggregate1 :: String -> Either String (NE.NonEmpty (BioFormula String))
parseBioAggregate1 str =
  case parse (white *> sepBy1 bioExpr comma <* eof) "" str of
    Left err -> Left (show err)
    Right [] -> Left "invalid empty aggregate"
    Right (x:xs) -> Right (x NE.:| xs)
