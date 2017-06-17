module GUI.Command
  ( AxRepr(..)
  , FrmlRepr(..)
  , BioAtoms
  , ReplaceAnswer(..)
  , GUIElemBase
  , GUICtrlSet
  , GUIControlType
  , GUIAxiom
  , GUIFormula
  , GUIAxEnv
  , GUIThrmEnv
  , GUICommand
  , Command(..)
  , Name(..)
  , UIF(..)
  , UI
  , AddedAxiom(..)
  , FEnv(..)
  , QueriedSeq(..)
  , Aggregate(..)
  , QueryAxioms(..)
  , AxNames(..)
  , AxName(..)
  , AxMode(..)
  , execCommand
  , execCommand'
  , aggregate1'
  , name
  , axiom
  , comma
  , neCtxt
  , axiomList
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
