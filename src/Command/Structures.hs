{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall #-}

module Command.Structures where

import Control.Monad (join)
import TypeClasses (filterOut, Pretty(..))
import Control.Monad.Free
import qualified Data.Map.Lazy as M
import qualified Data.Dequeue as D
import Data.Maybe (isJust)
import Data.Foldable (toList, foldlM)
import Data.Bifunctor (second)
import Rules hiding (reprAx, AxRepr)

newtype ThrmName = TN {unTN :: String} deriving (Eq, Ord, Show)
data AddedAxiom axr = AAx { unAAx :: axr }

instance Pretty ThrmName where
  pretty = unTN

data QueriedSeq frepr = QS
  { qsAxioms :: [ThrmName]
  , qsFrom :: frepr
  , qsTo :: frepr
  } deriving (Eq, Ord, Show)

instance Pretty frepr => Pretty (QueriedSeq frepr) where
  pretty (QS _ from to) = pretty from ++ " ==> " ++ pretty to

class CommAx axr ax where
  reprAx :: axr -> Either String ax

-- class CommFrml frepr frml | frml -> frepr where
--   reprFrml :: frepr -> Either String frml

class CParse  axr frepr where
  parseCommand :: String -> Either String (Command axr frepr)

class CPrint axr frepr | axr -> frepr, frepr -> axr where
  printAx :: ThrmName -> AddedAxiom axr -> String
  printThrm :: ThrmName -> QueriedSeq frepr -> String

data Command axr frepr
  = AddAxiom ThrmName axr
  | ChangeAxiom ThrmName axr
  | RemoveAxiom ThrmName
  | AddTheorem ThrmName (QueriedSeq frepr)
  | Query (QueriedSeq frepr)
  | LoadFile FilePath
  | SaveToFile FilePath
  deriving (Eq, Show)

type family DerT ax axr frepr :: *
-- type family SrchF (frml :: *) :: FKind -> *

class Search ax axr frepr where
  type SrchF ax axr frepr = (x :: FKind -> *) | x -> ax axr frepr --  :: FKind -> *
  fromRNS
    :: ResultNSequent
              (Ax (SrchF ax axr frepr))
                  (SrchF ax axr frepr)
                  (Cty (SrchF ax axr frepr))
    -> ThrmShape ax
  queryToGoal
    :: AxEnv axr ax
    -> ThrmEnv frepr ax
    -> QueriedSeq frepr
    -> Either String
        (GoalNSequent
          (Ax (SrchF ax axr frepr))
          (SrchF ax axr frepr))

-- class Search ax axr frepr | ax -> frml where
--   fromNS :: NSequent (Ax (SrchF frml)) (SrchF frml) (Cty (SrchF frml)) -> ThrmShape ax
--   queryToGoal
--     :: AxEnv axr ax
--     -> ThrmEnv frepr ax
--     -> QueriedSeq frepr
--     -> Either String (GoalNSequent (Ax (SrchF frml)) (SrchF frml) (Cty (SrchF frml)))

class (Pretty (TransRepr term)) => TransDerTerm term where
  type TransRepr term :: *
  transitions :: term -> [TransRepr term]

--------------------------------------------------------------------------------

newtype AxEnv axr ax =
  AE (M.Map ThrmName (AddedAxiom axr, ax))
newtype ThrmEnv frepr ax =
  TE (D.BankersDequeue (ThrmName, (QueriedSeq frepr, Maybe (ThrmShape ax))))

data ThrmShape ax = Axiomatic ax | NonAxiomatic
toMaybe :: ThrmShape ax -> Maybe ax
toMaybe (Axiomatic ax) = Just ax
toMaybe NonAxiomatic = Nothing

class FEnv env where
  type Elems env :: *
  feEmpty :: env
  feInsert :: ThrmName -> Elems env -> env -> Maybe env
  feRemove :: ThrmName -> env -> env
  feReplace :: ThrmName -> Elems env -> env -> env
  feLookup :: ThrmName -> env -> Maybe (Elems env)
  feAsList :: env -> [(ThrmName, Elems env)]

instance FEnv (ThrmEnv frepr ax) where
  type Elems (ThrmEnv frepr ax) = (QueriedSeq frepr, Maybe (ThrmShape ax))
  feEmpty = TE D.empty
  feInsert nm (q, sa) (TE thrms) =
    if isJust (lookup nm (toList thrms))
      then Nothing
      else Just (TE (D.pushBack thrms (nm, (q, sa))))
  feRemove name (TE thrms) =
    (TE (D.fromList . filter ((== name) . fst) . toList $ thrms))
  feReplace name x (TE thrms) =
    TE . D.fromList $ (replaceAssocL (name, x) (toList thrms))
  feLookup nm (TE thrms) = lookup nm (toList thrms)
  feAsList (TE thrms) = toList thrms

instance FEnv (AxEnv axr ax) where
  type Elems (AxEnv axr ax) = (AddedAxiom axr, ax)
  feEmpty = AE mempty
  feInsert n x (AE env) =
    if isJust (M.lookup n env)
       then Nothing
       else Just (AE (M.insert n x env))
  feRemove name (AE env) = AE (M.delete name env)
  feReplace n x (AE env) = AE (M.insert n x env)
  feLookup x (AE env) = M.lookup x env
  feAsList (AE m) = M.toList m

printAxAll :: CPrint axr frepr => AxEnv axr ax -> [String]
printAxAll (AE axs) = fmap ((uncurry printAx) . second fst) . M.toList $ axs

printThrmAll :: CPrint axr frepr => ThrmEnv frepr ax -> [String]
printThrmAll (TE thrms) = fmap (uncurry printThrm . second fst) . toList $ thrms

legitAxioms :: AxEnv axr ax -> ThrmEnv frepr ax -> [(ThrmName, ax)]
legitAxioms (AE axs) (TE thrms) = fromAxs ++ fromThrms
  where
    fromAxs = fmap (second snd) $ M.toList axs
    fromThrms =
      filterOut . fmap (aux . second (join . fmap toMaybe . snd)) . toList $ thrms
    aux (x, y) = y >>= \yy -> return (x, yy)

axsFromList
  :: AxEnv axr ax -> ThrmEnv frepr ax -> [ThrmName] -> Either String [ax]
axsFromList axs thrms names = do
  mapM mmm names
  where
    axioms = legitAxioms axs thrms
    mmm nm@(TN str) =
      maybe
        (Left $ "axioms '" ++ str ++ "' not in scope")
        Right
        (lookup nm axioms)

replaceAssocL
  :: Eq a
  => (a, b) -> [(a, b)] -> [(a, b)]
replaceAssocL _ [] = []
replaceAssocL (nm, x) ((nm', y):rest)
  | nm == nm' = (nm, x) : rest
  | otherwise = (nm', y) : (replaceAssocL (nm, x) rest)

processThrms
  :: (Monad m)
  => (ThrmName
        -> (QueriedSeq frepr, Maybe (ThrmShape ax))
        -> ThrmEnv frepr ax
        -> m (QueriedSeq frepr, Maybe (ThrmShape ax)))
  -> ThrmEnv frepr ax
  -> m (ThrmEnv frepr ax)
processThrms f (TE env) = foldlM f' feEmpty (toList env)
  where
    f' oldenv@ (TE queue) (nm,x) = do
      y <- f nm x oldenv
      return (TE (D.pushBack queue (nm, y)))

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
