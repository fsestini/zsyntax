{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}

{-# OPTIONS_GHC -Wall #-}

module Command.Structures where

import Control.Monad (join)
import TypeClasses (filterOut, Pretty(..))
import qualified Data.List.NonEmpty as NE
import Control.Monad.Free
import qualified Data.Map.Lazy as M
import SFormula hiding (ElemBase)
import qualified Data.Dequeue as D
import Data.Maybe (isJust)
import Data.Foldable (toList, foldlM)
import Data.Bifunctor (second)

--------------------------------------------------------------------------------
-- Command datatypes

newtype ThrmName = TN {unTN :: String} deriving (Eq, Ord, Show)
data AddedAxiom axr ctr = AAx axr ctr axr

data QueriedSeq axlistrepr frmlrepr = QS
  { axStr :: axlistrepr
  , fromStr :: frmlrepr
  , toStr :: frmlrepr
  } deriving (Eq, Ord, Show)

instance (Pretty axl, Pretty fr) => Pretty (QueriedSeq axl fr) where
  pretty (QS axs from to) =
    pretty axs ++ " ; " ++ pretty from ++ " ==> " ++ pretty to

instance Pretty ThrmName where
  pretty (TN name) = name

class ReprAx axrepr ctrepr cty a where
  reprAx :: axrepr -> ctrepr -> axrepr -> Either String (SAxiom cty a)

class ReprAxList axl where
  reprAxs :: axl -> Either String [ThrmName]

class ReprFrml fr a where
  reprFrml :: fr -> Either String (NE.NonEmpty (BioFormula a))

-- class ReprQS axr ctr axl fr eb cty a where
--   reprAxs :: [(ThrmName, SAxiom cty a)] -- AxEnv axr ctr cty a
--           -- -> ThrmEnv axl fr eb cty a
--           -> axl
--           -> Either String [SAxiom cty a]
--   reprFrml :: fr -> Either String (NE.NonEmpty (BioFormula a))

class CParse ctr axr fr axlr where
  parseCommand :: String
               -> Either String (Command ctr axr fr axlr)

class CPrintAx axr ctr where
  printAx :: ThrmName -> AddedAxiom axr ctr -> String

class CPrintThrm axl fr where
  printThrm :: ThrmName -> QueriedSeq axl fr -> String

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

newtype AxEnv axr ctr cty a =
  AE (M.Map ThrmName (AddedAxiom axr ctr, SAxiom cty a))
newtype ThrmEnv axlrepr frepr eb cty a =
  TE (D.BankersDequeue (ThrmName,
    (QueriedSeq axlrepr frepr,
      Maybe (Either (SAxiom cty a) (SFormula eb cty a)))))

class FEnv env where
  type Elems env :: *
  feEmpty :: env
  feInsert :: ThrmName -> Elems env -> env -> Maybe env
  feRemove :: ThrmName -> env -> env
  feReplace :: ThrmName -> Elems env -> env -> env
  feLookup :: ThrmName -> env -> Maybe (Elems env)
  feAsList :: env -> [(ThrmName, Elems env)]

instance FEnv (ThrmEnv axlrepr frepr eb cty a) where
  type Elems (ThrmEnv axlrepr frepr eb cty a) =
    (QueriedSeq axlrepr frepr, Maybe (Either (SAxiom cty a) (SFormula eb cty a)))
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

instance FEnv (AxEnv axr ctr cty a) where
  type Elems (AxEnv axr ctr cty a) = (AddedAxiom axr ctr, SAxiom cty a)
  feEmpty = AE mempty
  feInsert n x (AE env) =
    if isJust (M.lookup n env)
       then Nothing
       else Just (AE (M.insert n x env))
  feRemove name (AE env) = AE (M.delete name env)
  feReplace n x (AE env) = AE (M.insert n x env)
  feLookup x (AE env) = M.lookup x env
  feAsList (AE m) = M.toList m

printAxAll :: CPrintAx axr ctr => AxEnv axr ctr cty a -> [String]
printAxAll (AE axs) = fmap ((uncurry printAx) . second fst) . M.toList $ axs

printThrmAll :: CPrintThrm axl fr => ThrmEnv axl fr eb cty a -> [String]
printThrmAll (TE thrms) = fmap (uncurry printThrm . second fst) . toList $ thrms

legitAxioms :: AxEnv axr ctr cty a
            -> ThrmEnv axl fr eb cty a
            -> [(ThrmName, SAxiom cty a)]
legitAxioms (AE axs) (TE thrms) = fromAxs ++ fromThrms
  where
    fromAxs = fmap (second snd) $ M.toList axs
    fromThrms =
      filterOut .
      fmap (aux . second (join . fmap (either Just (const Nothing)) . snd)) $
      toList thrms
    aux (x, y) = y >>= \yy -> return (x, yy)

axsFromList
  :: (ReprAxList axl)
  => AxEnv axr ctr cty a
  -> ThrmEnv axl fr eb cty a
  -> axl
  -> Either String [SAxiom cty a]
axsFromList axs thrms list = do
  names <- reprAxs list
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
  => (ThrmName -> (QueriedSeq axl fr, Maybe (Either (SAxiom cty a) (SFormula eb cty a)))
        -> ThrmEnv axl fr eb cty a
        -> m (QueriedSeq axl fr, Maybe (Either (SAxiom cty a) (SFormula eb cty a))))
  -> ThrmEnv axl fr eb cty a
  -> m (ThrmEnv axl fr eb cty a)
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
