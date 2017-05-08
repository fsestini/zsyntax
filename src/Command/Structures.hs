{-# LANGUAGE DeriveFunctor #-}

{-# OPTIONS_GHC -Wall #-}

module Command.Structures where

import Control.Monad.Free
import qualified Data.Map as M
import SFormula
import Checking

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

type Env = M.Map String (SAxiom SimpleElemBase SimpleCtrlSet String)
type ThrmEnv = M.Map ThrmName QueriedSeq

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
