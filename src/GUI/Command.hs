module GUI.Command
  ( AxRepr(..)
  , FrmlRepr(..)
  , BioAtoms
  , GUIElemBase
  , GUICtrlSet
  , GUIControlType
  , GUIAxiom
  , GUIFormula
  , GUIAxEnv
  , GUIThrmEnv
  , GUICommand
  , Command(..)
  , ThrmName(..)
  , UIF(..)
  , UI
  , AddedAxiom(..)
  , FEnv(..)
  , QueriedSeq(..)
  , Aggregate(..)
  , execCommand
  , execCommand'
  , aggregate1'
  , thrmName
  , comma
  , neCtxt
  , axiomList
  , prettys
  ) where

import Command.Structures
import Command.Execution
import CLI.Command

type GUICommand = CLICommand
type GUIElemBase = CLIElemBase
type GUIAxiom = CLIAxiom
type GUIFormula = CLIFormula
type GUICtrlSet = CLICtrlSet
type GUIControlType = CLIControlType
type GUIAxEnv = CLIAxEnv
type GUIThrmEnv = CLIThrmEnv
