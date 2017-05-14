{-# OPTIONS_GHC -Wall #-}

module Command.Parser (parseCommand) where

import Text.Parsec.Char
import Text.Parsec hiding (State, token)
import Text.Parsec.String
import Data.List

import Command.Structures

--------------------------------------------------------------------------------
-- Command parsing

parseCommand :: String -> Either ParseError Command
parseCommand = parse command ""

thrmName :: Parser ThrmName
thrmName = TN <$> many1 alphaNum

aggregate1 :: Parser String
aggregate1 =
  concat . intersperse "," <$> a1

aggregate :: Parser String
aggregate =
  concat . intersperse "," <$> a

a1 :: Parser [String]
a1 = sepBy1 (try (token (many1 (noneOf [',', '(', ')'])))) (try comma)

a :: Parser [String]
a = sepBy (try (token (many1 (noneOf [',', '(', ')'])))) (try comma)

-- add axiom name (aggr...) (aggr...) unless (aggr...)
parseAddAxiom :: Parser Command
parseAddAxiom = token (string "add") >> token (string "axiom") >> do
  name <- token thrmName
  from <- parens (aggregate1)
  spaces
  to <- parens (aggregate1)
  _ <- token (string "unless")
  ctrlset <- parens (aggregate)
  return $ AddAxiom name (CSS ctrlset) from to

parseEditAxiom :: Parser Command
parseEditAxiom = token (string "change") >> token (string "axiom") >> do
  name <- token thrmName
  from <- parens (aggregate1)
  spaces
  to <- parens (aggregate1)
  _ <- token (string "unless")
  ctrlset <- parens (aggregate)
  return $ ChangeAxiom name (CSS ctrlset) from to

-- query name (aggr...) (aggr...) with axioms (...)
parseQueryTheorem :: Parser Command
parseQueryTheorem =
  token (string "query") >> do
    maybeName <- fmap Just (try (token thrmName)) <|> return Nothing
    from <- parens (aggregate1)
    spaces
    to <- parens (aggregate1)
    _ <- token (string "with axioms")
    axioms <- parens (aggregate)
    let q = QS (AS axioms) from to
    case maybeName of
      Just name -> return $ AddTheorem name q
      Nothing -> return $ Query q

parseLoadFile :: Parser Command
parseLoadFile =
  token (string "load file") >> LoadFile <$> token (many1 (noneOf [' ']))

parseSaveToFile :: Parser Command
parseSaveToFile =
  token (string "save to file") >> SaveToFile <$> many1 (noneOf [' '])

parseRemoveAxiom :: Parser Command
parseRemoveAxiom =
  RemoveAxiom <$> (token (string "remove axiom") >> (token thrmName))

command :: Parser Command
command =
  parseAddAxiom <|> parseEditAxiom <|> parseQueryTheorem <|> parseLoadFile <|>
  parseSaveToFile <|> parseRemoveAxiom

comma :: Parser Char
comma = token (char ',')

parens :: Parser a -> Parser a
parens p = token (char '(') *> p <* token (char ')')

token :: Parser a -> Parser a
token p = spaces >> p
