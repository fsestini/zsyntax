module GUI.Control where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Layout.HBox
import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, writeIORef, readIORef)
import Control.Monad (forM_)
import Control.Monad.Free (foldFree)
import Text.Parsec
import Data.Bifunctor
import qualified TypeClasses as T
import qualified Data.List.NonEmpty as NE

import Data.Char
import Data.List

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
    (("Name", T.pretty . fst) NE.:| [("Formula", prettyAA . fst . snd)])

  -- Separator
  addSep vbox

  -- Theorems list
  thList <- theoremArea vbox
    (("Name", T.pretty . fst) NE.:| [("Theorem", T.pretty . fst . snd)])

  let gui = GUI thList (storeAxioms axioms) b

  wireThrmEntry gui state thrmEntry
  wireAxiomsArea gui state axioms

  widgetShowAll w
  on w deleteEvent $ liftIO mainQuit >> return False
  mainGUI

prettyAA :: AddedAxiom AxRepr -> String
prettyAA (AAx (AR from _ to)) = T.pretty from ++ " ---> " ++ T.pretty to

parseThrmNames :: String -> Either String [ThrmName]
parseThrmNames =
  bimap show id . parse (sepBy (spaces *> thrmName <* spaces) comma <* eof) ""

wireThrmEntry :: GUI -> IORef AppState -> TheoremEntryArea -> IO ()
wireThrmEntry gui state tea = do
  onClicked (btnGo tea) $
    thrmAreaToCommand (eName tea) (eAxioms tea) (eFrom tea) (eTo tea) >>=
    either (printError gui) (execCommandInGUI gui state)
  onClicked (btnLoad tea) $
    loadFileCommand >>= maybe (return ()) (execCommandInGUI gui state)
  onClicked (btnExport tea) $
    saveFileCommand >>= maybe (return ()) (execCommandInGUI gui state)
  return ()

printError :: GUI -> String -> IO ()
printError gui str = appendLog (logBuffer gui) ("error: " ++ str)

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

askAddAxiom :: IO (Maybe GUICommand)
askAddAxiom = do
  res <- axiomsDialog "Add axiom..." Nothing
  flip (maybe (return Nothing)) res $ \adc -> do
    return . Just $
      AddAxiom
        (name adc)
        (AR (from . repr $ adc) (ctrl . repr $ adc) (to . repr $ adc))

-- TODO: pass actual data, not Nothing
askEditAxiom :: IO (Maybe GUICommand)
askEditAxiom = do
  res <- axiomsDialog "Change axiom..." Nothing
  flip (maybe (return Nothing)) res $ \adc -> do
    return . Just $
      ChangeAxiom
        (name adc)
        (AR (from . repr $ adc) (ctrl . repr $ adc) (to . repr $ adc))

appendLog :: TextBuffer -> String -> IO ()
appendLog b str = do
  i <- textBufferGetEndIter b
  textBufferInsert b i (str ++ "\n")

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

thrmAreaToCommand :: Entry -> Entry -> Entry -> Entry
                  -> IO (Either String GUICommand)
thrmAreaToCommand nmE axE fromE toE = do
  nmTxt <- entryGetText nmE
  axTxt <- entryGetText axE
  fromTxt <- entryGetText fromE
  toTxt <- entryGetText toE
  return $ do
    axs <- parseThrmNames axTxt
    from <- bimap show id . parseAggregate $ fromTxt
    to <- bimap show id . parseAggregate $ toTxt
    if null (trim nmTxt)
      then return $ Query (QS axs (Aggr from) (Aggr to))
      else return $ AddTheorem (TN nmTxt) (QS axs (Aggr from) (Aggr to))

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace


-- thrmAreaToCommand :: Entry -> Entry -> Entry -> Entry
--                   -> IO (Either String GUICommand)
-- thrmAreaToCommand nmE axE fromE toE = do
--   nmTxt <- entryGetText nmE :: IO String
--   axTxt <- entryGetText axE :: IO String
--   fromTxt <- entryGetText fromE :: IO String
--   toTxt <- entryGetText toE :: IO String
--   if null (trim nmTxt)
--      then return $ Query (QS (AS axTxt) fromTxt toTxt)
--      else return $ AddTheorem (TN nmTxt) (QS (AS axTxt) fromTxt toTxt)

interpret :: GUI -> UIF a -> IO a
interpret gui (UILog str x) = appendLog (logBuffer gui) str >> return x
interpret _ (UILoadFile path x) = fmap x (readFile path)
interpret _ (UISaveFile path content x) = writeFile path content >> return x

toIO :: GUI -> UI a -> IO a
toIO gui = foldFree (interpret gui)

loadFileCommand :: IO (Maybe GUICommand)
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

saveFileCommand :: IO (Maybe GUICommand)
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
