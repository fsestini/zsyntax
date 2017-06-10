{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wall #-}

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
       (BioFormula(..), SrchFormula, LGoalNSequent, decideN,
        decideOF, LAxiom(..), bConj)
import Rules hiding (AxRepr, AR)
import Parser
import Data.Char (isSpace)
import Data.List (dropWhileEnd, intersperse)
import Data.Foldable (toList)
import Data.Bifunctor (bimap)
import qualified TypeClasses as T
import qualified SimpleDerivationTerm as SDT
import Control.Newtype

newtype CLI a = CLI a deriving (Eq, Ord, Show, T.Pretty)

instance Newtype (CLI a) a where { pack = CLI ; unpack (CLI x) = x }

newtype Aggregate = Aggr (NE.NonEmpty (BioFormula BioAtoms))
  deriving (Eq, Ord, Show)

instance Newtype Aggregate (NE.NonEmpty (BioFormula BioAtoms))
  where { pack = Aggr ; unpack (Aggr a) = a }

instance T.Pretty Aggregate where
  pretty = T.prettys . unpack

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
type CLIAxiom = CLI (S.SAxiom CLIControlType BioAtoms)
-- The particular fully applied type of formulas that are used in the user
-- interface.
type CLIFormula = CLI (S.SFormula CLIElemBase CLIControlType String)

type CLIAxEnv = AxEnv AxRepr CLIAxiom
type CLIThrmEnv = ThrmEnv Aggregate CLIAxiom

type CLIDerTerm = SDT.SimpleDerTerm BioAtoms

newtype CLITransRepr = SimpleTransRepr BioAtoms

type CLISrchFormula = SrchFormula CLIElemBase CLIControlType BioAtoms Int

type instance DerT CLIAxiom AxRepr FrmlRepr = CLIDerTerm

instance Search CLIAxiom AxRepr FrmlRepr where
  type SrchF CLIAxiom AxRepr FrmlRepr = CLISrchFormula
  fromRNS (RNS _ lc cty concl) =
    maybe NonAxiomatic Axiomatic $ do
      nelc <- mapM decideN $ toNEList lc
      toFrml <- decideOF concl
      return $ CLI (S.fromBasicNS nelc cty toFrml)
  queryToGoal axs thrms (QS axlist q1 q2) = do
    axioms <-
      case names axlist of
        Some list -> axsFromList axs thrms list
        AllOfEm -> return (fmap snd (legitAxioms axs thrms))
    let lc = fmap S.sAtom . unpack $ q1
        concl = foldr1 S.sConj . fmap S.sAtom . unpack $ q2
        sq = S.SQ (fromFoldable (fmap unpack axioms)) (fromNEList lc) concl
        gns = fst $ runState (unPM . neutralize $ sq) 0
    return gns
  toAx = CLI . S.srchAxToSax
  mergeAx (CLI (S.SA (LAx a c b _))) (CLI (S.SA (LAx a' c' b' _))) =
    CLI (S.SA (LAx (bConj a a' ()) (c <> c') (bConj b b' ()) ()))

instance SearchDump CLIAxiom AxRepr FrmlRepr where
  goalDiff ns@(NS _ lc1 _ concl1) (GNS _ lc2 concl2) =
    if nsIdentity ns then 0 else
      uncurry (+) (bimap
        (uncurry (+) . (bimap length length))
        (uncurry (+) . (bimap length length)) diffs)
    where
      co1 = cToLC concl1
      co2 = cToLC concl2
      diffs =
        ( T.eiFirstSecond . fmap toList $ (eq' lc1 (toLC lc2))
        , T.eiFirstSecond . fmap toList $ (eq' co1 co2))
  pprintSeq (NS _ lc1 _ concl) (GNS _ lc2 _) =
    (if (not . null $ d2)
       then " >> " ++ T.prettys d2 ++ " << "
       else "") ++
    (if (not . null $ d1)
       then " << " ++ T.prettys d1 ++ " >> "
       else "") ++
    T.prettys comm ++
    " ===> " ++
    T.prettys (cToLC concl)
    where
      (EI d1 d2 comm) = fmap toList (eq' lc1 (toLC lc2))

cToLC :: Opaque CLISrchFormula -> LinearCtxt (Opaque (SrchF CLIAxiom AxRepr FrmlRepr))
cToLC = either (singleton . neutralToOpaque) fromFoldable . maybeNeutral

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
  reprAx (AR fromAggr ctrl' toAggr) = do
    return . CLI $
      S.sAx
        (foldr1 S.bsConj . fmap S.bsAtom . unpack $ fromAggr)
        (foldr1 S.bsConj . fmap S.bsAtom . unpack $ toAggr)
        (RL [(mempty, ctrl')])

--------------------------------------------------------------------------------
-- Command parsing

type CLICommand = Command AxRepr FrmlRepr

instance CParse AxRepr FrmlRepr where
  pCommand = command

name :: Parser Name
name = NM <$> many1 alphaNum

aggregate1' :: Parser (NE.NonEmpty (BioFormula BioAtoms))
aggregate1' = do
  aggr <- sepBy1 (bioExpr <* spaces) (comma <* spaces)
  case aggr of
    [] -> unexpected "invalid empty aggregate"
    (x:xs) -> return (x NE.:| xs)

parenAggr :: Parser (NE.NonEmpty (BioFormula BioAtoms))
parenAggr = parens (token aggregate1')

neCtxt :: Parser (NonEmptyLinearCtxt (BioFormula BioAtoms))
neCtxt = fromNEList <$> aggregate1'

ctrlCtxt :: Parser (CtrlSetCtxt BioAtoms)
ctrlCtxt =  try (string "regular" >> fmap Regular neCtxt)
        <|> (string "super" >> fmap SupsetClosed neCtxt)

ctrlSet :: Parser (CtrlSet BioAtoms)
ctrlSet = parens (token pCtxts)
  where pCtxts = do
          ctxts <- many (parens (token ctrlCtxt) <* spaces)
          return (fromFoldableCtxts ctxts)

-- str axiom name (aggr...) (aggr...) unless ((regular ...) (super ...) ...)
parseAxiom :: String -> Parser CLICommand
parseAxiom str = string str >> token (string "axiom") >> do
  name <- token name
  fromAggr <- token parenAggr
  toAggr <- token parenAggr
  _ <- token (string "unless")
  ctrlset <- token ctrlSet
  return $ AddAxiom name (AR (Aggr fromAggr) ctrlset (Aggr toAggr))

axiomList :: Parser [Name]
axiomList = parens (token pList)
  where
    pList = sepBy (name <* spaces) (comma <* spaces)

queryAxioms :: AxMode -> Parser QueryAxioms
queryAxioms m = try allParser <|> try someParser
  where
    allParser :: Parser QueryAxioms
    allParser =
      string "all" >> spaces >> string "axioms" >> return (QA AllOfEm m)
    someParser :: Parser QueryAxioms
    someParser =
      string "axioms" >> spaces >> (flip QA m . Some <$> axiomList)

queryAxMode :: Parser AxMode
queryAxMode = try (string "refine" >> return Refine) <|> return Normal

-- query name (aggr...) (aggr...) [refine] with axioms (...)
queryTheorem :: Parser CLICommand
queryTheorem =
  string "query" >> do
    maybeName <- fmap Just (try (token name)) <|> return Nothing
    fromAggr <- token parenAggr
    toAggr <- token parenAggr
    m <- token queryAxMode
    _ <- token (string "with")
    qAxs <- token (queryAxioms m)
    let q = QS qAxs (Aggr fromAggr) (Aggr toAggr)
    case maybeName of
      Just name -> return $ AddTheorem name q
      Nothing -> return $ Query q

url :: Parser FilePath
url = many1 (noneOf [' '])

parseLoadFile :: Parser CLICommand
parseLoadFile = string "load file" >> spaces >> LoadFile <$> url

parseOpenFile :: Parser CLICommand
parseOpenFile = string "open file" >> spaces >> OpenFile <$> url

btwSpaces :: [String] -> Parser ()
btwSpaces = foldr1 (>>) . intersperse spaces . fmap ((>> return ()) . string)

parseSaveToFile :: Parser CLICommand
parseSaveToFile = btwSpaces ["save", "to", "file"] >> SaveToFile <$> token url

parseRemoveAxiom :: Parser CLICommand
parseRemoveAxiom =
  btwSpaces ["remove", "axiom"] >> RemoveAxioms <$> fmap return (token name)

command :: Parser CLICommand
command = commands <?> "a command name"
  where
    commands =
      try (parseAxiom "add") <|>
      try (parseAxiom "change") <|>
      try queryTheorem <|>
      try parseLoadFile <|>
      try parseOpenFile <|>
      try parseSaveToFile <|>
      try parseRemoveAxiom

comma :: Parser Char
comma = char ','

parens :: Parser a -> Parser a
parens p = char '(' *> p <* char ')'

token :: Parser a -> Parser a
token p = spaces >> p

--------------------------------------------------------------------------------
-- Export

instance CPrint AxRepr FrmlRepr where
  printAx = exportAxiom
  printThrm = exportTheorem

exportAxiom :: Name -> AddedAxiom AxRepr -> String
exportAxiom (NM name) (AAx (AR fromAggr cty toAggr)) =
  "add axiom " ++ name ++ " (" ++ T.pretty fromAggr ++ ") (" ++ T.pretty toAggr
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

exportTheorem :: Name -> QueriedSeq FrmlRepr -> String
exportTheorem (NM name) (QS axs fromAggr toAggr) =
  "query " ++ name ++ " (" ++
  T.pretty fromAggr ++ ") (" ++ T.pretty toAggr ++ ")" ++ qMode ++ " with " ++ qAxs
  where
    qMode =
      case mode axs of
        Refine -> " refine"
        Normal -> ""
    qAxs =
      case names axs of
        AllOfEm -> "all axioms"
        Some list -> "axioms (" ++ T.prettys list ++ ")"

--------------------------------------------------------------------------------

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace
