module GUI.Control where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Layout.HBox
import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, writeIORef, readIORef)
import Control.Monad
import Control.Arrow ((>>>))
import Control.Monad.Free (foldFree)
import Text.Parsec
import Data.Bifunctor
import qualified TypeClasses as T
import qualified Data.List.NonEmpty as NE

import Utils (trim, maySingleton)
import Data.Time
import Data.Char
import Data.List
import Safe
import qualified LinearContext as LC

import Checking.ReactLists.Sets

import GUI.Elements
import GUI.Command
-- import Command.Structures
import Debug.Trace

type AppState = (GUIAxEnv, GUIThrmEnv)
type AxItem = (ThrmName, Elems GUIAxEnv)
type ThrmItem = (ThrmName, Elems GUIThrmEnv)

data GUI = GUI
  { thrmsStore :: ListStore ThrmItem
  , axiomsStore :: ListStore AxItem
  , logBuffer :: TextBuffer
  }

gui :: IO ()
gui = do
  state <- newIORef ((feEmpty, feEmpty) :: AppState)
  initGUI
  w <- windowNew
  set w [ windowTitle := "Zsyntax"
        , windowDefaultWidth := 500
        , windowDefaultHeight := 500
        , containerBorderWidth := 10 ]

  vbox <- vBoxNew False 0
  set w [ containerChild := vbox ]

  -- Theorem area
  thrmEntry <- theoremEntryArea vbox

  addSep vbox

  -- Log area
  b <- logArea vbox

  -- Separator
  addSep vbox

  -- Axioms list
  axioms <- axiomsArea vbox
    (("Name", T.pretty . fst) NE.:|
      [("Formula", prettyAA . fst . snd)
      ,("Control set", pprintCtrlSet . ctrl . unAAx . fst . snd)])

  -- Separator
  addSep vbox

  -- Theorems list
  thList <- theoremArea vbox
    (("Name", T.pretty . fst) NE.:|
    [("Theorem", T.pretty . fst . snd)
    ,("Axioms", prettyQAxs . qsAxioms . fst . snd)
    ,("Provable", maybe "No" (const "Yes") . snd . snd)])

  let gui = GUI thList (storeAxioms axioms) b

  wireThrmEntry gui state thrmEntry
  wireAxiomsArea gui state axioms

  widgetShowAll w
  on w deleteEvent $ liftIO mainQuit >> return False
  mainGUI

parseThrmNames :: String -> Either String [ThrmName]
parseThrmNames =
  bimap show id . parse (sepBy (spaces *> thrmName <* spaces) comma <* eof) ""

wireThrmEntry :: GUI -> IORef AppState -> TheoremEntryArea -> IO ()
wireThrmEntry gui state tea = do
  onClicked (btnGo tea) $ do
    useList <- toggleButtonGetActive (rbSome tea)
    thrmAreaToCommand (eName tea) (eAxioms tea) (eFrom tea) (eTo tea) useList >>=
      either (printError gui) (execCommandInGUI gui state)
  onClicked (btnOpen tea) $
    maybeMM' openFileCommand (execCommandInGUI gui state)
  onClicked (btnLoad tea) $
    maybeMM' loadFileCommand (execCommandInGUI gui state)
  onClicked (btnExport tea) $
    maybeMM' saveFileCommand (execCommandInGUI gui state)
  return ()

printError :: GUI -> String -> IO ()
printError gui str = appendLog (logBuffer gui) ("error: " ++ str)

wireAxiomsArea :: GUI -> IORef AppState -> AxiomsArea AxItem -> IO ()
wireAxiomsArea gui state axioms = do
  onClicked (btnAddAxiom axioms) $
    maybeMM' askAddAxiom (execCommandInGUI gui state)
  onClicked (btnChangeAxiom axioms) $
    maybeMM'
      (selectedAxiom axioms)
      (askEditAxiom . toADC >=> maybeM (execCommandInGUI gui state))
  onClicked (btnRemoveAxiom axioms) $
    maybeMM'
      (selectedAxioms axioms)
      ((execCommandInGUI gui state . RemoveAxioms) . fmap fst)
  return ()
  where
    toADC :: AxItem -> AxDiaContent
    toADC (name, (AAx ar, _)) = ADC name ar

selectedAxiom :: AxiomsArea AxItem -> IO (Maybe AxItem)
selectedAxiom axioms = do
  sel <- treeSelectionGetSelectedRows (treeSelAxioms axioms)
  maybe' (join (fmap headMay (maySingleton sel))) (return Nothing) $ \i -> do
    item <- listStoreGetValue (storeAxioms axioms) i
    return (Just item)

selectedAxioms :: AxiomsArea AxItem -> IO (Maybe [AxItem])
selectedAxioms axioms =
  treeSelectionGetSelectedRows (treeSelAxioms axioms) >>=
    mapM (mapM (listStoreGetValue (storeAxioms axioms))) . mapM headMay

askAddAxiom :: IO (Maybe GUICommand)
askAddAxiom =
  maybeP (axiomsDialog "Add axiom..." Nothing) $ \adc ->
    Just $ AddAxiom (name adc)
      (AR (from . repr $ adc) (ctrl . repr $ adc) (to . repr $ adc))

askEditAxiom :: AxDiaContent -> IO (Maybe GUICommand)
askEditAxiom content =
  maybeP (axiomsDialog "Change axiom..." (Just content)) $ \adc ->
    Just $ ChangeAxiom (name adc)
      (AR (from . repr $ adc) (ctrl . repr $ adc) (to . repr $ adc))

appendLog :: TextBuffer -> String -> IO ()
appendLog b str = do
  i <- textBufferGetEndIter b
  time <- getCurrentTime
  textBufferInsert b i
    (formatTime defaultTimeLocale "%F %T" time ++ ": " ++ str ++ "\n")

execCommandInGUI :: GUI -> IORef AppState -> GUICommand -> IO ()
execCommandInGUI gui state c = do
  (ax,th) <- readIORef state
  (newAx, newTh) <- toIO gui $ execCommand' c ax th
  writeIORef state (newAx, newTh)
  resetStore (axiomsStore gui) (feAsList newAx)
  resetStore (thrmsStore gui) (feAsList newTh)

resetStore :: ListStore a -> [a] -> IO ()
resetStore store list =
  listStoreClear store >> forM_ list (listStoreAppend store)

thrmAreaToCommand :: Entry -> Entry -> Entry -> Entry -> Bool
                  -> IO (Either String GUICommand)
thrmAreaToCommand nmE axE fromE toE useList = do
  nmTxt <- entryGetText nmE
  axTxt <- entryGetText axE
  fromTxt <- entryGetText fromE
  toTxt <- entryGetText toE
  return $ do
    axs <- if useList then Some <$> parseThrmNames axTxt else return AllOfEm
    from <- bimap show id . parseAggregate $ fromTxt
    to <- bimap show id . parseAggregate $ toTxt
    if null (trim nmTxt)
      then return $ Query (QS axs (Aggr from) (Aggr to))
      else return $ AddTheorem (TN nmTxt) (QS axs (Aggr from) (Aggr to))

interpret :: GUI -> UIF a -> IO a
interpret gui (UILog str x) = appendLog (logBuffer gui) str >> return x
interpret _ (UILoadFile path x) = fmap x (readFile path)
interpret _ (UISaveFile path content x) = writeFile path content >> return x

toIO :: GUI -> UI a -> IO a
toIO gui = foldFree (interpret gui)

openFileCommand :: IO (Maybe GUICommand)
openFileCommand = do
  fileD <- fileChooserDialogNew (Just "Open file...") Nothing
    FileChooserActionOpen [("Cancel", ResponseCancel), ("Open", ResponseAccept)]
  widgetShow fileD
  response <- dialogRun fileD
  c <- case response of
         ResponseAccept ->
           fileChooserGetFilename fileD >>= (fmap OpenFile >>> return)
         _ -> return Nothing
  widgetDestroy fileD
  return c

loadFileCommand :: IO (Maybe GUICommand)
loadFileCommand = do
  fileD <- fileChooserDialogNew (Just "Load file...") Nothing
    FileChooserActionOpen [("Cancel", ResponseCancel), ("Load", ResponseAccept)]
  widgetShow fileD
  response <- dialogRun fileD
  c <- case response of
         ResponseAccept ->
           fileChooserGetFilename fileD >>= (fmap LoadFile >>> return)
         _ -> return Nothing
  widgetDestroy fileD
  return c

saveFileCommand :: IO (Maybe GUICommand)
saveFileCommand = do
  fileD <- fileChooserDialogNew (Just "Save file as...") Nothing
    FileChooserActionSave [("Cancel", ResponseCancel), ("Save", ResponseAccept)]
  widgetShow fileD
  response <- dialogRun fileD
  c <- case response of
         ResponseAccept -> do
           fileChooserGetFilename fileD >>= (fmap SaveToFile >>> return)
         _ -> return Nothing
  widgetDestroy fileD
  return c

--------------------------------------------------------------------------------
-- Pretty-printers

pprintCtrlSetCtxt :: (T.Pretty a, Ord a) => CtrlSetCtxt a -> String
pprintCtrlSetCtxt (Regular ctxt) =
  "regular: " ++ LC.asFoldable T.prettys ctxt
pprintCtrlSetCtxt (SupsetClosed ctxt) =
  "supset-closed: " ++ LC.asFoldable T.prettys ctxt

pprintCtrlSet :: (T.Pretty a, Ord a) => CtrlSet a -> String
pprintCtrlSet = concat . intersperse "; " . fmap pprintCtrlSetCtxt . toCtxtList

prettyAA :: AddedAxiom AxRepr -> String
prettyAA (AAx (AR from _ to)) = T.pretty from ++ " → " ++ T.pretty to

prettyQAxs :: QueryAxioms -> String
prettyQAxs AllOfEm = "all"
prettyQAxs (Some list) = T.prettys list

--------------------------------------------------------------------------------

maybe' :: Maybe a -> b -> (a -> b) -> b
maybe' x y z = maybe y z x

maybeM :: Monad m => (a -> m ()) -> Maybe a -> m ()
maybeM = maybe (return ())

maybeM' :: Monad m => Maybe a -> (a -> m ()) -> m ()
maybeM' m f = maybe' m (return ()) f

maybeMM' :: Monad m => m (Maybe a) -> (a -> m ()) -> m ()
maybeMM' mm f = mm >>= maybeM f

maybeMM'' :: Monad m => m (Maybe a) -> m b -> (a -> m b) -> m b
maybeMM'' m z s = m >>= maybe z s

maybeP :: (Monad m, MonadPlus p) => m (Maybe a) -> (a -> p b) -> m (p b)
maybeP m s = maybeMM'' m (return mzero) (return . s)
