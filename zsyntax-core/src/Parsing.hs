{-| Globally useful utility functions for parsing. -}
module Parsing
  ( padded
  , spaces
  , parseString
  , sepBy1'
  , Parser
  , ParseError
  ) where

import Text.Parsec.Char (spaces)
import Text.Parsec (ParseError, parse, sepBy1)
import Text.Parsec.String (Parser)

import qualified Data.List.NonEmpty as NE

padded :: Parser a -> Parser a
padded p = spaces *> p <* spaces

parseString :: Parser a -> String -> Either ParseError a
parseString p = parse p ""

sepBy1' :: Parser a -> Parser b -> Parser (NE.NonEmpty a)
sepBy1' p sep = do
  (x : xs) <- sepBy1 p sep
  return (x NE.:| xs)
