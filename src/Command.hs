{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}

module Command
  ( Command(..)
  , AxEnv
  , ThrmEnv
  , UIF(..)
  , UI
  , ThrmName(..)
  , CSString(..)
  , AxiomsString(..)
  , QueriedSeq(..)
  -- , foldFree
  , execCommand
  , execCommand'
  , parseCommand
  , feEmpty
  , feAsList
  , trim
  , SA
  , SF
  ) where

import Command.Structures
import Command.Parser
import Command.Execution

-- checkSplit :: String -> Either String (NE.NonEmpty String)
-- checkSplit str =
--   case splitOn "," (trim str) of
--     [] -> Left "cannot have empty aggregate"
--     (x:xs) -> Right $ x NE.:| xs

-- boh
--   :: (String -> Either ParseError (SFormula eb SimpleCtrlSet String))
--   -> NE.NonEmpty String
--   -> Either ParseError (SFormula eb SimpleCtrlSet String)
-- boh f l = fmap (foldr1 sConj) $ forM l f

-- -- execFromState :: Command -> Env -> Free UIF Env
-- -- execFromState c = fmap snd . runStateT (execCommand c)
