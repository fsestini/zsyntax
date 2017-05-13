{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}

{-# OPTIONS_GHC -Wall #-}

module Command.Structures where

import Control.Monad.Free
import qualified Data.Map as M
import SFormula
import Checking
import qualified Data.Dequeue as D
import Data.Maybe (isNothing, isJust)
import Data.Foldable (toList, foldlM)

--------------------------------------------------------------------------------
-- Command datatypes

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

type SA = SAxiom SimpleElemBase SimpleCtrlSet String
newtype AxEnv = AE (M.Map ThrmName SA)
newtype ThrmEnv = TE (D.BankersDequeue (ThrmName, (QueriedSeq, Maybe SA)))

class FEnv env where
  type Elems env :: *
  feEmpty :: env
  feInsert :: ThrmName -> Elems env -> env -> Maybe env
  feLookup :: ThrmName -> env -> Maybe (Elems env)
  feAsList :: env -> [(ThrmName, Elems env)]

instance FEnv ThrmEnv where
  type Elems ThrmEnv = (QueriedSeq, Maybe SA)
  feEmpty = TE D.empty
  feInsert nm (q, sa) (TE thrms) =
    if isJust (lookup nm (toList thrms))
      then Nothing
      else Just (TE (D.pushBack thrms (nm, (q, sa))))
  feLookup nm (TE thrms) = lookup nm (toList thrms)
  feAsList (TE thrms) = toList thrms

instance FEnv AxEnv where
  type Elems AxEnv = SA
  feEmpty = AE mempty
  feInsert n x (AE env) =
    if isJust (M.lookup n env)
       then Nothing
       else Just (AE (M.insert n x env))
  feLookup x (AE env) = M.lookup x env
  feAsList (AE m) = M.toList m

processThrms
  :: (Monad m)
  => (ThrmName -> (QueriedSeq, Maybe SA) -> ThrmEnv -> m (QueriedSeq, Maybe SA))
  -> ThrmEnv
  -> m ThrmEnv
processThrms f (TE env) = foldlM f' (TE env) (toList env)
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
