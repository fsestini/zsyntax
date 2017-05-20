module GUI.Command
  ( AxList(..)
  , FrmlArea(..)
  , AxArea(..)
  , CtrlArea(..)
  , BioAtoms
  , GUIElemBase
  , GUICtrlType
  , GUIControlType
  , GUIAxiom
  , GUIFormula
  , GUIAxEnv
  , GUIThrmEnv
  , GUICommand
  , Command(..)
  , ThrmName(..)
  , QueriedSeq(..)
  , Elems
  , UIF(..)
  , UI
  , execCommand
  , execCommand'
  , aggregate1'
  , thrmName
  , comma
  , neCtxt
  , axiomList
  ) where

import Command.Structures
import Command.Execution
import CLI.Command

type GUICommand = CLICommand
type GUIElemBase = UIElemBase
type GUICtrlType = UICtrlType
type GUIAxiom = UIAxiom
type GUIFormula = UIFormula
type GUIControlType = ControlType
type GUIAxEnv = CLIAxEnv
type GUIThrmEnv = CLIThrmEnv
