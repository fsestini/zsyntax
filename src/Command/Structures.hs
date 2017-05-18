{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}

{-# OPTIONS_GHC -Wall #-}

module Command.Structures where

import Control.Monad.Free
import qualified Data.Map as M
import SFormula hiding (ElemBase, CtrlSet)
import Checking.ReactLists.RList
import Checking.ReactLists.Sets
import qualified Data.Dequeue as D
import Data.Maybe (isJust)
import Data.Foldable (toList, foldlM)

--------------------------------------------------------------------------------
-- Command datatypes

newtype ThrmName = TN {unTN :: String} deriving (Eq, Ord)
newtype CSString = CSS {unCSS :: String} deriving (Eq, Ord, Show)
newtype AxiomsString = AS String deriving (Eq, Ord, Show)

data QueriedSeq axlistrepr frmlrepr = QS
  { axStr :: axlistrepr
  , fromStr :: frmlrepr
  , toStr :: frmlrepr
  } deriving (Eq, Ord, Show)

instance Show ThrmName where
  show (TN name) = name

class Repr a b where
  repr :: a -> b

data Command ctrepr axrepr frmlrepr axlistrepr
  = AddAxiom ThrmName
             ctrepr
             axrepr
             axrepr
  | ChangeAxiom ThrmName
                ctrepr
                axrepr
                axrepr
  | RemoveAxiom ThrmName
  | AddTheorem ThrmName
               (QueriedSeq axlistrepr frmlrepr)
  | Query (QueriedSeq axlistrepr frmlrepr)
  | LoadFile FilePath
  | SaveToFile FilePath
  deriving (Eq, Show)

type BioAtoms = String
type UIElemBase = ElemBase
type UICtrlType = CtrlSet
type ControlType = RList UIElemBase CtrlSet
-- The particular fully applied type of axioms that are used in the user
-- interface.
type UIAxiom = SAxiom ControlType BioAtoms
-- The particular fully applied type of formulas that are used in the user
-- interface.
type UIFormula = SFormula UIElemBase ControlType String
newtype AxEnv = AE (M.Map ThrmName UIAxiom)
newtype ThrmEnv axlrepr frepr =
  TE (D.BankersDequeue (ThrmName, (QueriedSeq axlrepr frepr, Maybe (Either UIAxiom UIFormula))))

class FEnv env where
  type Elems env :: *
  feEmpty :: env
  feInsert :: ThrmName -> Elems env -> env -> Maybe env
  feRemove :: ThrmName -> env -> env
  feReplace :: ThrmName -> Elems env -> env -> env
  feLookup :: ThrmName -> env -> Maybe (Elems env)
  feAsList :: env -> [(ThrmName, Elems env)]

instance FEnv (ThrmEnv axlrepr frepr) where
  type Elems (ThrmEnv axlrepr frepr) =
    (QueriedSeq axlrepr frepr, Maybe (Either UIAxiom UIFormula))
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

instance FEnv AxEnv where
  type Elems AxEnv = UIAxiom
  feEmpty = AE mempty
  feInsert n x (AE env) =
    if isJust (M.lookup n env)
       then Nothing
       else Just (AE (M.insert n x env))
  feRemove name (AE env) = AE (M.delete name env)
  feReplace n x (AE env) = AE (M.insert n x env)
  feLookup x (AE env) = M.lookup x env
  feAsList (AE m) = M.toList m

replaceAssocL
  :: Eq a
  => (a, b) -> [(a, b)] -> [(a, b)]
replaceAssocL _ [] = []
replaceAssocL (nm, x) ((nm', y):rest)
  | nm == nm' = (nm, x) : rest
  | otherwise = (nm', y) : (replaceAssocL (nm, x) rest)

processThrms
  :: (Monad m)
  => (ThrmName -> (QueriedSeq axl fr, Maybe (Either UIAxiom UIFormula))
        -> ThrmEnv axl fr
        -> m (QueriedSeq axl fr, Maybe (Either UIAxiom UIFormula)))
  -> ThrmEnv axl fr
  -> m (ThrmEnv axl fr)
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
