{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CLI.Command where

import Text.Parsec.Char
import Text.Parsec.Prim (unexpected)
import Text.Parsec hiding (State, token)
import Text.Parsec.String

import LinearContext
import qualified Data.List.NonEmpty as NE
import Command.Structures
import Checking.ReactLists.RList
import Checking.ReactLists.Sets
import qualified SFormula as S
import qualified RelFormula as L
import Parser
import Control.Monad (join)
import Data.List (intersperse)
import Data.List.Split (splitOn)
import Data.Char (isSpace)
import Data.List (dropWhileEnd)
import Data.Foldable (toList)
import RelFormula (BioFormula)
import Data.Bifunctor (bimap)
import Context
import qualified TypeClasses as T

newtype AxList = AL [ThrmName] deriving (Show)
newtype FrmlArea = FA
  { unFA :: NE.NonEmpty (BioFormula BioAtoms)
  } deriving (Show)
-- TODO: probably useless to have a separate AxArea type. use FrmlArea.
newtype AxArea = AA { unAA :: NE.NonEmpty (BioFormula BioAtoms) } deriving (Show)
newtype CtrlArea = CA (CtrlSet BioAtoms) deriving (Show)

instance T.Pretty FrmlArea where
  pretty = concat . intersperse "," . fmap T.pretty . NE.toList . unFA

instance T.Pretty AxArea where
  pretty = concat . intersperse "," . fmap T.pretty . NE.toList . unAA

instance T.Pretty AxList where
  pretty (AL list) = concat . intersperse "," . fmap T.pretty $ list

type BioAtoms = String
type UIElemBase = ElemBase
type UICtrlType = CtrlSet
type ControlType = RList UIElemBase CtrlSet
-- The particular fully applied type of axioms that are used in the user
-- interface.
type UIAxiom = S.SAxiom ControlType BioAtoms
-- The particular fully applied type of formulas that are used in the user
-- interface.
type UIFormula = S.SFormula UIElemBase ControlType String

type CLIAxEnv = AxEnv AxArea CtrlArea ControlType BioAtoms
type CLIThrmEnv = ThrmEnv AxList FrmlArea UIElemBase ControlType BioAtoms

instance ReprAx AxArea CtrlArea ControlType BioAtoms where
  reprAx (AA from) (CA ctrl) (AA to) = do
    return $
      S.sAx
        (foldr1 S.bsConj . fmap S.bsAtom $ from)
        (foldr1 S.bsConj . fmap S.bsAtom $ to)
        (RL [(mempty, ctrl)])

instance ReprAxList AxList where
  reprAxs (AL axs) = return axs

instance ReprFrml FrmlArea BioAtoms where
  reprFrml (FA area) = return area

--------------------------------------------------------------------------------
-- Command parsing

type CLICommand = Command CtrlArea AxArea FrmlArea AxList

instance CParse CtrlArea AxArea FrmlArea AxList where
  parseCommand = bimap show id . CLI.Command.parseCommand

parseCommand :: String -> Either ParseError CLICommand
parseCommand = parse command ""

thrmName :: Parser ThrmName
thrmName = TN <$> many1 alphaNum

-- aggregate1 :: Parser String
-- aggregate1 = concat . intersperse "," <$> a1

aggregate1' :: Parser (NE.NonEmpty (BioFormula BioAtoms))
aggregate1' = do
  aggr <- sepBy1 (token bioExpr) comma
  case aggr of
    [] -> unexpected "invalid empty context in control set"
    (x:xs) -> return (x NE.:| xs)

-- aggregate :: Parser String
-- aggregate =
--   concat . intersperse "," <$> a

-- a1 :: Parser [String]
-- a1 = sepBy1 (try (token (many1 (noneOf [',', '(', ')'])))) (try comma)

-- a :: Parser [String]
-- a = sepBy (try (token (many1 (noneOf [',', '(', ')'])))) (try comma)

neCtxt :: Parser (LinearCtxt (BioFormula BioAtoms))
neCtxt = do
  aggr <- aggregate1'
  let ctxt = fromFoldable aggr :: LinearCtxt (BioFormula BioAtoms)
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
  return $ AddAxiom name (CA ctrlset) (AA from) (AA to)

axiomList :: Parser [ThrmName]
axiomList = sepBy ((spaces *> thrmName <* spaces)) comma

-- query name (aggr...) (aggr...) with axioms (...)
queryTheorem :: Parser CLICommand
queryTheorem =
  token (string "query") >> do
    maybeName <- fmap Just (try (token thrmName)) <|> return Nothing
    from <- parens (aggregate1')
    spaces
    to <- parens (aggregate1')
    _ <- token (string "with axioms")
    axioms <- parens axiomList
    let q = QS (AL axioms) (FA from) (FA to)
    case maybeName of
      Just name -> return $ AddTheorem name q
      Nothing -> return $ Query q

parseLoadFile :: Parser CLICommand
parseLoadFile =
  token (string "load file") >> LoadFile <$> token (many1 (noneOf [' ']))

parseSaveToFile :: Parser CLICommand
parseSaveToFile =
  token (string "save to file") >> SaveToFile <$> many1 (noneOf [' '])

parseRemoveAxiom :: Parser CLICommand
parseRemoveAxiom =
  RemoveAxiom <$> (token (string "remove axiom") >> (token thrmName))

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

instance CPrintAx AxArea CtrlArea where
  printAx = exportAxiom

instance CPrintThrm AxList FrmlArea where
  printThrm = exportTheorem

-- exportAxiom :: ThrmName -> AddedAxiom AxArea CtrlArea -> String
-- exportAxiom (TN name) (SA (ImplF from _ cty to _)) =
--   "add axiom " ++ name ++ " (" ++ aux aggr1 ++ ") (" ++ aux aggr2
--   ++ ") unless (" ++ exportCtrl cty ++ ")"
--   where
--     aggr1 = bfToAtoms from
--     aggr2 = bfToAtoms to
--     aux = concat . intersperse "," . fmap ppBioFormula


exportAxiom :: ThrmName -> AddedAxiom AxArea CtrlArea -> String
exportAxiom (TN name) (AAx (AA from) (CA cty) (AA to)) =
  "add axiom " ++ name ++ " (" ++ aux from ++ ") (" ++ aux to
  ++ ") unless (" ++ exportCtrl cty ++ ")"

ppBioFormula :: BioFormula BioAtoms -> String
ppBioFormula (L.BioAtom x) = T.pretty x
ppBioFormula (L.BioInter x y) = ppBioFormula x ++ " <> " ++ ppBioFormula y

exportCtrl :: CtrlSet BioAtoms -> String
exportCtrl =
  concat . fmap (\s -> "(" ++ s ++ ")") . fmap exportCtrlCtxt . toCtxtList

exportCtrlCtxt :: CtrlSetCtxt BioAtoms -> String
exportCtrlCtxt (Regular ctxt) = "regular " ++ aux list
  where
    list :: [BioFormula BioAtoms]
    list = asFoldable toList ctxt
exportCtrlCtxt (SupsetClosed ctxt) = "super " ++ aux list
  where
    list :: [BioFormula BioAtoms]
    list = asFoldable toList ctxt

aux :: Foldable f => f (BioFormula BioAtoms) -> String
aux = concat . intersperse "," . fmap ppBioFormula . toList

exportTheorem :: ThrmName -> QueriedSeq AxList FrmlArea -> String
exportTheorem (TN name) (QS (AL axStr) (FA fromStr) (FA toStr)) =
  "query " ++
  name ++
  " (" ++ aux fromStr ++ ") (" ++ aux toStr ++ ") with axioms (" ++
  (concat . intersperse "," . fmap unTN $ axStr) ++ ")"

--------------------------------------------------------------------------------

  -- reprAx (AA fromStr) ctrlArea (AA toStr) = do
  --   ctrl <- parseCtrl ctrlArea
  --   from <- parseBioAggregate1 fromStr
  --   to <- parseBioAggregate1 toStr
  --   return $
  --     S.sAx
  --       (foldr1 S.bsConj . fmap S.bsAtom $ from)
  --       (foldr1 S.bsConj . fmap S.bsAtom $ to)
  --       ctrl

  -- reprAxs axs thrms (AL axioms) =
  --   mapM (parseAxiomStr axs thrms) (splitTrim axioms)
  -- reprFrml (FA string) = parseBioAggregate1 string

-- parseCtrl :: CtrlArea -> Either String (ControlType BioAtoms)
-- parseCtrl = undefined

-- parseAxiomStr :: CLIAxEnv -> CLIThrmEnv -> ThrmName -> Either String UIAxiom
-- parseAxiomStr env thrms nm@(TN str) =
--   case feLookup nm env <|>
--        (join . fmap (join . fmap (either Just (const Nothing)) . snd) $
--         feLookup nm thrms) of
--     Nothing -> Left $ "axiom '" ++ str ++ "' not in scope"
--     Just ax -> Right ax

-- splitTrim :: String -> [String]
-- splitTrim str = filter (not . null) $ map trim $ splitOn "," (trim str)

-- trim :: String -> String
-- trim = dropWhileEnd isSpace . dropWhile isSpace
