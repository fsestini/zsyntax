module GUI.Control where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Layout.HBox
import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, writeIORef, readIORef)
import Control.Monad (forM_)
import Control.Monad.Free (foldFree)

import GUI.Elements

import Command
import Debug.Trace

type AppState = (AxEnv, ThrmEnv)
type AxItem = (ThrmName, SA)
type ThrmItem = (ThrmName, (QueriedSeq, Maybe (Either SA SF)))

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
        , windowDefaultWidth := 1000
        , windowDefaultHeight := 600
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
  axioms <- axiomsArea vbox show

  -- Separator
  addSep vbox

  -- Theorems list
  thList <- theoremArea vbox show

  let gui = GUI thList (storeAxioms axioms) b

  wireThrmEntry gui state thrmEntry
  wireAxiomsArea gui state axioms

  widgetShowAll w
  on w deleteEvent $ liftIO mainQuit >> return False
  mainGUI

wireThrmEntry :: GUI -> IORef AppState -> TheoremEntryArea -> IO ()
wireThrmEntry gui state tea = do
  onClicked (btnGo tea) $
    thrmAreaToCommand (eName tea) (eAxioms tea) (eFrom tea) (eTo tea) >>=
    execCommandInGUI gui state
  onClicked (btnLoad tea) $
    loadFileCommand >>= maybe (return ()) (execCommandInGUI gui state)
  onClicked (btnExport tea) $
    saveFileCommand >>= maybe (return ()) (execCommandInGUI gui state)
  return ()

wireAxiomsArea :: GUI -> IORef AppState -> AxiomsArea AxItem -> IO ()
wireAxiomsArea gui state axioms = do
  onClicked (btnAddAxiom axioms) $
    askAddAxiom >>= maybe (return ()) (execCommandInGUI gui state)
  onClicked (btnChangeAxiom axioms) $
    askEditAxiom >>= maybe (return ()) (execCommandInGUI gui state)
  onClicked (btnRemoveAxiom axioms) $ do
    sel <- treeSelectionGetSelectedRows (treeSelAxioms axioms)
    (name, _) <- listStoreGetValue (storeAxioms axioms) (head (head sel))
    execCommandInGUI gui state (RemoveAxiom name)
  return ()

askAddAxiom :: IO (Maybe Command)
askAddAxiom = do
  res <- axiomsDialog "Add axiom..." emptyADC
  flip (maybe (return Nothing) ) res $ \adc -> do
    return . Just $ AddAxiom (name adc) (ctrl adc) (from adc) (to adc)

askEditAxiom :: IO (Maybe Command)
askEditAxiom = do
  res <- axiomsDialog "Change axiom..." emptyADC
  flip (maybe (return Nothing)) res $ \adc -> do
    return . Just $ ChangeAxiom (name adc) (ctrl adc) (from adc) (to adc)

appendLog :: TextBuffer -> String -> IO ()
appendLog b str = do
  i <- textBufferGetEndIter b
  textBufferInsert b i (str ++ "\n")

execCommandInGUI :: GUI -> IORef AppState -> Command -> IO ()
execCommandInGUI gui state c = traceShow c $ do
  (ax,th) <- readIORef state
  (newAx, newTh) <- toIO gui $ execCommand' c ax th
  writeIORef state (newAx, newTh)
  resetStore (axiomsStore gui) (feAsList newAx)
  resetStore (thrmsStore gui) (feAsList newTh)

resetStore :: ListStore a -> [a] -> IO ()
resetStore store list =
  listStoreClear store >> forM_ list (listStoreAppend store)

thrmAreaToCommand :: Entry -> Entry -> Entry -> Entry -> IO Command
thrmAreaToCommand nmE axE fromE toE = do
  nmTxt <- entryGetText nmE :: IO String
  axTxt <- entryGetText axE :: IO String
  fromTxt <- entryGetText fromE :: IO String
  toTxt <- entryGetText toE :: IO String
  if null (trim nmTxt)
     then return $ Query (QS (AS axTxt) fromTxt toTxt)
     else return $ AddTheorem (TN nmTxt) (QS (AS axTxt) fromTxt toTxt)

interpret :: GUI -> UIF a -> IO a
interpret gui (UILog str x) = appendLog (logBuffer gui) str >> return x
interpret _ (UILoadFile path x) = fmap x (readFile path)
interpret _ (UISaveFile path content x) = writeFile path content >> return x

toIO :: GUI -> UI a -> IO a
toIO gui = foldFree (interpret gui)

loadFileCommand :: IO (Maybe Command)
loadFileCommand = do
  fileD <- fileChooserDialogNew (Just "Load file...") Nothing
    FileChooserActionOpen [("Cancel", ResponseCancel), ("Load", ResponseAccept)]
  widgetShow fileD
  response <- dialogRun fileD
  c <- case response of
         ResponseAccept -> do
           fileName <- fileChooserGetFilename fileD
           return (fmap LoadFile fileName)
         _ -> return Nothing
  widgetDestroy fileD
  return c

saveFileCommand :: IO (Maybe Command)
saveFileCommand = do
  fileD <- fileChooserDialogNew (Just "Save file as...") Nothing
    FileChooserActionSave [("Cancel", ResponseCancel), ("Save", ResponseAccept)]
  widgetShow fileD
  response <- dialogRun fileD
  c <- case response of
         ResponseAccept -> do
           fileName <- fileChooserGetFilename fileD
           return (fmap SaveToFile fileName)
         _ -> return Nothing
  widgetDestroy fileD
  return c
