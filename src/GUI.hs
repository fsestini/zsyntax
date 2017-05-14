module GUI where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Layout.HBox
import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, writeIORef, readIORef)
import Control.Monad (forM_)
import Control.Monad.Free (foldFree)

import Command
import Debug.Trace

type AppState = (AxEnv, ThrmEnv)
type AxItem = (ThrmName, SA)
type ThrmItem = (ThrmName, (QueriedSeq, Maybe SA))

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
  (teName, teAxioms, teFrom, teTo, teBtn, openBtn, exportBtn)
    <- theoremArea vbox

  -- Separator
  sep1 <- hSeparatorNew
  boxPackStart vbox sep1 PackNatural 10

  -- Log area
  scroll <- scrolledWindowNew Nothing Nothing
  b <- textBufferNew Nothing
  tv <- textViewNewWithBuffer b
  textViewSetEditable tv False
  scrolledWindowAddWithViewport scroll tv
  boxPackStart vbox scroll PackGrow 0

  -- Separator
  sep2 <- hSeparatorNew
  boxPackStart vbox sep2 PackNatural 10

  -- Axioms list
  axLabel <- labelNew (Just "Axioms:")
  miscSetAlignment axLabel 0 0
  boxPackStart vbox axLabel PackNatural 3

  list <- listStoreNew []
  tree <- treeViewNewWithModel list
  treeViewSetHeadersVisible tree True
  col <- treeViewColumnNew
  renderer <- cellRendererTextNew
  cellLayoutPackStart col renderer True
  cellLayoutSetAttributes col renderer list $ \row -> [ cellText := (show row) ]
  _ <- treeViewAppendColumn tree col
  treeViewColumnSetTitle col "My data"

  treeSel <- treeViewGetSelection tree
  treeSelectionSetMode treeSel SelectionSingle

  axHb <- hBoxNew False 10
  boxPackStart axHb tree PackGrow 0

  axBtnsVb <- vBoxNew False 0
  addAxBtn <- buttonNewWithLabel "Add axiom"
  boxPackStart axBtnsVb addAxBtn PackNatural 0
  editAxBtn <- buttonNewWithLabel "Edit axiom"
  boxPackStart axBtnsVb editAxBtn PackNatural 0
  removeAxBtn <- buttonNewWithLabel "Remove axiom"
  boxPackStart axBtnsVb removeAxBtn PackNatural 0
  boxPackStart axHb axBtnsVb PackNatural 0
  boxPackStart vbox axHb PackGrow 0

  -- Separator
  sep3 <- hSeparatorNew
  boxPackStart vbox sep3 PackNatural 10

  thLabel <- labelNew (Just "Theorems:")
  miscSetAlignment thLabel 0 0
  boxPackStart vbox thLabel PackNatural 3

  thList <- listStoreNew []
  thTree <- treeViewNewWithModel thList
  treeViewSetHeadersVisible thTree True
  thCol <- treeViewColumnNew
  thRenderer <- cellRendererTextNew
  cellLayoutPackStart thCol thRenderer True
  cellLayoutSetAttributes thCol thRenderer thList $ \row -> [ cellText := show row ]
  _ <- treeViewAppendColumn thTree thCol
  treeViewColumnSetTitle thCol "My data"

  boxPackStart vbox thTree PackGrow 0

  let gui = GUI thList list b

  onClicked teBtn $
    thrmAreaToCommand teName teAxioms teFrom teTo >>= execCommandInGUI gui state

  onClicked addAxBtn $
    askAddAxiom >>= maybe (return ()) (execCommandInGUI gui state)

  onClicked editAxBtn $
    askEditAxiom >>= maybe (return ()) (execCommandInGUI gui state)

  onClicked removeAxBtn $ do
    sel <- treeSelectionGetSelectedRows treeSel
    (name, _) <- listStoreGetValue list (head (head sel))
    execCommandInGUI gui state (RemoveAxiom name)

  onClicked openBtn $
    loadFileCommand >>= maybe (return ()) (execCommandInGUI gui state)
  onClicked exportBtn $ appendLog b "save file as"

  widgetShowAll w
  on w deleteEvent $ liftIO mainQuit >> return False
  mainGUI

askAddAxiom :: IO (Maybe Command)
askAddAxiom = addEditAxiom AddAxiom "Add axiom"

askEditAxiom :: IO (Maybe Command)
askEditAxiom = addEditAxiom ChangeAxiom "Edit axiom"

addEditAxiom
  :: (ThrmName -> CSString -> String -> String -> Command)
  -> String
  -> IO (Maybe Command)
addEditAxiom ctor title = do
  dia <- dialogNew
  set
    dia
    [ windowTitle := title
    , windowDefaultWidth := 400
    , windowDefaultHeight := 300
    ]
  dialogAddButton dia stockApply ResponseApply
  dialogAddButton dia stockCancel ResponseCancel
  upbox <- dialogGetUpper dia
  axNmE <- titledEntry upbox "Name: "
  axFromE <- titledEntry upbox "Start aggregate: "
  axToE <- titledEntry upbox "Result aggregate: "
  axCtrlE <- titledEntry upbox "Control set: "
  widgetShowAll upbox
  answer <- dialogRun dia
  result <-
    if answer == ResponseApply
      then do
        nmTxt <- entryGetText axNmE
        fromTxt <- entryGetText axFromE
        toTxt <- entryGetText axToE
        ctrlTxt <- entryGetText axCtrlE
        return . Just $ ctor (TN nmTxt) (CSS ctrlTxt) fromTxt toTxt
      else return Nothing
  widgetDestroy dia
  return result
  where
    titledEntry :: VBox -> String -> IO Entry
    titledEntry vbox str = do
      l <- labelNew (Just str)
      hb <- hBoxNew False 0
      boxPackStart hb l PackNatural 5
      entry <- entryNew
      boxPackStart hb entry PackGrow 5
      boxPackStart vbox hb PackGrow 0
      return entry


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
interpret _ _ = error "not implemented yet"

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

--------------------------------------------------------------------------------

theoremArea :: VBox -> IO (Entry, Entry, Entry, Entry, Button, Button, Button)
theoremArea vbox = do
  packLabel vbox "Prove theorem:"
  teName <- entryNew
  set teName [entryEditable := True]
  teAxioms <- entryNew
  set teAxioms [entryEditable := True]
  teFrom <- entryNew
  set teFrom [entryEditable := True]
  teTo <- entryNew
  set teTo [entryEditable := True]
  teBtn <- buttonNewWithLabel "Go"
  openBtn <- buttonNewWithLabel "Open file..."
  exportBtn <- buttonNewWithLabel "Export..."
  hb <- hBoxNew False 0
  boxPackStart vbox hb PackNatural 0
  packLabel hb "Name:"
  boxPackStart hb teName PackNatural 0
  packLabel hb "Axioms:"
  boxPackStart hb teAxioms PackGrow 5
  packLabel hb "Start aggr.:"
  boxPackStart hb teFrom PackGrow 5
  packLabel hb "End aggr.:"
  boxPackStart hb teTo PackGrow 5
  boxPackStart hb teBtn PackNatural 3
  boxPackStart hb openBtn PackNatural 3
  boxPackStart hb exportBtn PackNatural 3
  return (teName, teAxioms, teFrom, teTo, teBtn, openBtn, exportBtn)

packLabel box str = do
  l <- labelNew (Just str)
  miscSetAlignment l 0 0
  boxPackStart box l PackNatural 3
