module GUI.Control where

import System.IO
import Graphics.UI.Gtk
import Graphics.UI.Gtk.Layout.HBox
import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, writeIORef, readIORef)
import Control.Monad
import Control.Arrow ((>>>))
import Control.Monad.Free (foldFree)
import Control.Newtype
import Text.Parsec
import Data.Bifunctor
import qualified TypeClasses as T
import qualified Data.List.NonEmpty as NE

import Utils (trim, maySingleton)
import Parsing
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
type AxItem = (Name, Elems GUIAxEnv)
type ThrmItem = (Name, Elems GUIThrmEnv)

data GUI = GUI
  { thrmsStore :: ListStore ThrmItem
  , axiomsStore :: ListStore AxItem
  , logBuffer :: TextBuffer
  , putThrm :: ThrmItem -> IO ()
  , clearThrmEntry :: IO ()
  , mainWindow :: Window
  }

gui :: IO ()
gui = do
  state <- newIORef ((feEmpty, feEmpty) :: AppState)
  initGUI
  w <- windowNew
  set w [ windowTitle := "Zsyntax"
        , windowDefaultWidth := 600
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
  axioms <- axiomsArea vbox
    (("Name", T.pretty . fst) NE.:|
      [("Formula", prettyAA . fst . snd)
      ,("Control set", pprintCtrlSet . ctrl . unAAx . fst . snd)])

  -- Separator
  addSep vbox

  -- Theorems list
  theorems <- theoremArea vbox
            (("Name", T.pretty . fst) NE.:|
            [("Theorem", T.pretty . fst . snd)
            ,("Axioms", prettyAxNames . names . qsAxioms . fst . snd)
            ,("Provable", maybe "No" (const "Yes") . snd . snd)])

  let gui =
        GUI (storeThrms theorems)
            (storeAxioms axioms)
            b
            (copyThrm thrmEntry)
            (clearThrmEntryArea thrmEntry)
            w

  wireThrmEntry gui state thrmEntry
  wireAxiomsArea gui state axioms
  wireThrmArea gui state theorems

  widgetShowAll w
  on w deleteEvent $ liftIO mainQuit >> return False
  mainGUI

copyThrm :: TheoremEntryArea -> ThrmItem -> IO ()
copyThrm teArea ((NM name), (qs, _)) = do
  entrySetText (eName teArea) name
  case names . qsAxioms $ qs of
    AllOfEm -> toggleButtonSetActive (rbAll teArea) True
    Some axs ->
      entrySetText (eAxioms teArea) (join . intersperse "," . fmap T.pretty $ axs)
  entrySetText (eFrom teArea) (T.pretty . qsFrom $ qs :: String)
  entrySetText (eTo teArea) (T.pretty . qsTo $ qs)

parseAxNames :: String -> Either ParseError [AxName]
parseAxNames = parseString (spaces *> axiomList <* (spaces >> eof))

wireThrmEntry :: GUI -> IORef AppState -> TheoremEntryArea -> IO ()
wireThrmEntry gui state tea = do
  onClicked (btnGo tea) $ do
    useList <- toggleButtonGetActive (rbSome tea)
    m <-
      toggleButtonGetActive (chkRefine tea) >>= \b ->
        if b
          then return Refine
          else return Normal
    thrmAreaToCommand (eName tea) (eAxioms tea) (eFrom tea) (eTo tea) useList m >>=
      either (printError gui) (execCommandInGUI gui state)
  onClicked (btnOpen tea) $
    maybeMM' openFileCommand (execCommandInGUI gui state)
  onClicked (btnLoad tea) $
    maybeMM' loadFileCommand (execCommandInGUI gui state)
  onClicked (btnExport tea) $
    maybeMM' saveFileCommand (execCommandInGUI gui state)
  onClicked (btnClear tea) $
    clearThrmEntry gui >> execCommandInGUI gui state Clear
  return ()

clearThrmEntryArea :: TheoremEntryArea -> IO ()
clearThrmEntryArea tea = do
  entrySetText (eName tea) ""
  entrySetText (eAxioms tea) ""
  entrySetText (eFrom tea) ""
  entrySetText (eTo tea) ""

printError :: GUI -> String -> IO ()
printError gui str = appendLog (logBuffer gui) ("error: " ++ str)

wireAxiomsArea :: GUI -> IORef AppState -> AxiomsArea AxItem -> IO ()
wireAxiomsArea gui state axioms = do
  onClicked (btnAddAxiom axioms) $
    maybeMM' (askAddAxiom (mainWindow gui)) (execCommandInGUI gui state)
  onClicked (btnChangeAxiom axioms) $
    maybeMM'
      (fmap join . fmap (fmap headMay) $
       selected (storeAxioms axioms) (treeSelAxioms axioms))
      ((askEditAxiom (mainWindow gui)) . toADC >=>
       maybeM (execCommandInGUI gui state))
  onClicked (btnRemoveAxiom axioms) $
    maybeMM'
      (selected (storeAxioms axioms) (treeSelAxioms axioms))
      ((execCommandInGUI gui state . RemoveAxioms) . fmap fst)
  return ()
  where
    toADC :: AxItem -> AxDiaContent
    toADC (name, (AAx ar, _)) = ADC name ar

askAddAxiom :: Window -> IO (Maybe GUICommand)
askAddAxiom parent =
  maybeP (axiomsDialog parent "Add axiom..." Nothing) $ \adc ->
    Just $ AddAxiom (adcName adc)
      (AR (from . adcRepr $ adc) (ctrl . adcRepr $ adc) (to . adcRepr $ adc))

askEditAxiom :: Window -> AxDiaContent -> IO (Maybe GUICommand)
askEditAxiom parent content =
  maybeP (axiomsDialog parent "Change axiom..." (Just content)) $ \adc ->
    Just $ ChangeAxiom (adcName adc)
      (AR (from . adcRepr $ adc) (ctrl . adcRepr $ adc) (to . adcRepr $ adc))

--------------------------------------------------------------------------------
-- Theorem area

wireThrmArea :: GUI -> IORef AppState -> TheoremsArea ThrmItem -> IO ()
wireThrmArea gui state thrms = do
  onClicked (btnRefreshThrms thrms) (execCommandInGUI gui state RefreshTheorems)
  onClicked (btnCopyThrm thrms) $
    selected (storeThrms thrms) (treeSelThrms thrms) >>=
    maybeM (putThrm gui) . join . fmap headMay
  onClicked (btnRemoveThrm thrms) $
    maybeMM'
      (selected (storeThrms thrms) (treeSelThrms thrms))
      ((execCommandInGUI gui state . RemoveTheorems) . fmap fst)
  return ()

--------------------------------------------------------------------------------

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

thrmAreaToCommand :: Entry -> Entry -> Entry -> Entry -> Bool -> AxMode
                  -> IO (Either String GUICommand)
thrmAreaToCommand nmE axE fromE toE useList m = do
  nmTxt <- entryGetText nmE :: IO String
  axTxt <- entryGetText axE
  fromTxt <- entryGetText fromE
  toTxt <- entryGetText toE
  return $ do
    realName <-
      bimap show id (parse (spaces *> many alphaNum <* spaces <* eof) "" nmTxt)
    axs <-
      if useList
        then Some <$> bimap show id (parseAxNames axTxt)
        else return AllOfEm
    from <- bimap show id . parseAggregate $ fromTxt
    to <- bimap show id . parseAggregate $ toTxt
    if null (trim realName)
      then return $ Query (QS (QA axs m) (Aggr from) (Aggr to))
      else return $
           AddTheorem (NM realName) (QS (QA axs m) (Aggr from) (Aggr to))

interpret :: GUI -> UIF a -> IO a
interpret gui (UILog str x) = appendLog (logBuffer gui) str >> return x
interpret gui (UIError str x) =
  -- TODO: use dialog
  appendLog (logBuffer gui) ("error: " ++ str) >> return x
interpret gui (UIAskReplaceThrm name x) =
  askReplaceThrm (mainWindow gui) name >>= return . x
interpret _ (UILoadFile path x) = fmap x (readFile path)
interpret _ (UISaveFile path content x) = writeFile path content >> return x
interpret _ (UIStdErr str x) = hPutStrLn stderr str >> return x

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

prettyAxNames :: AxNames -> String
prettyAxNames AllOfEm = "all"
prettyAxNames (Some list) = T.prettys list

--------------------------------------------------------------------------------

selected :: ListStore t -> TreeSelection -> IO (Maybe [t])
selected store treeSel =
  treeSelectionGetSelectedRows treeSel >>=
  mapM (mapM (listStoreGetValue store)) . mapM headMay

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
