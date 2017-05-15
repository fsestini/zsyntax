module GUI.Elements where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Layout.HBox
import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, writeIORef, readIORef)
import Control.Monad (forM_)
import Control.Monad.Free (foldFree)

import Command.Structures (ThrmName(..), CSString(..))

--------------------------------------------------------------------------------

data AxDiaContent = ADC
  { name :: ThrmName
  , from :: String
  , to :: String
  , ctrl :: CSString
  }

emptyADC = ADC (TN "") "" "" (CSS "")

axiomsDialog :: String -> AxDiaContent -> IO (Maybe AxDiaContent)
axiomsDialog title content = do
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
  entrySetText axNmE (unTN . name $ content)
  axFromE <- titledEntry upbox "Start aggregate: "
  entrySetText axFromE (from content)
  axToE <- titledEntry upbox "Result aggregate: "
  entrySetText axToE (to content)
  axCtrlE <- titledEntry upbox "Control set: "
  entrySetText axCtrlE (unCSS . ctrl $ content)
  answer <- dialogRun dia
  result <-
    if answer == ResponseApply
      then do
        nmTxt <- entryGetText axNmE
        fromTxt <- entryGetText axFromE
        toTxt <- entryGetText axToE
        ctrlTxt <- entryGetText axCtrlE
        return . Just $ ADC (TN nmTxt) fromTxt toTxt (CSS ctrlTxt)
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

--------------------------------------------------------------------------------

addSep :: VBox -> IO ()
addSep vbox = hSeparatorNew >>= \s -> boxPackStart vbox s PackNatural 10

--------------------------------------------------------------------------------

logArea :: VBox -> IO TextBuffer
logArea vbox = do
  scroll <- scrolledWindowNew Nothing Nothing
  b <- textBufferNew Nothing
  tv <- textViewNewWithBuffer b
  textViewSetEditable tv False
  scrolledWindowAddWithViewport scroll tv
  boxPackStart vbox scroll PackGrow 0
  return b

--------------------------------------------------------------------------------

theoremArea :: VBox -> (t -> String) -> IO (ListStore t)
theoremArea vbox render = do
  thLabel <- labelNew (Just "Theorems:")
  miscSetAlignment thLabel 0 0
  boxPackStart vbox thLabel PackNatural 3
  thList <- listStoreNew []
  thTree <- treeViewNewWithModel thList
  treeViewSetHeadersVisible thTree True
  thCol <- treeViewColumnNew
  thRenderer <- cellRendererTextNew
  cellLayoutPackStart thCol thRenderer True
  cellLayoutSetAttributes thCol thRenderer thList $
    \row -> [cellText := render row]
  _ <- treeViewAppendColumn thTree thCol
  treeViewColumnSetTitle thCol "My data"
  boxPackStart vbox thTree PackGrow 0
  return thList

--------------------------------------------------------------------------------

data AxiomsArea t = AA
  { btnAddAxiom :: Button
  , btnChangeAxiom :: Button
  , btnRemoveAxiom :: Button
  , storeAxioms :: ListStore t
  , treeSelAxioms :: TreeSelection
  }

axiomsArea :: VBox -> (t -> String) -> IO (AxiomsArea t)
axiomsArea vbox render = do
  axLabel <- labelNew (Just "Axioms:")
  miscSetAlignment axLabel 0 0
  boxPackStart vbox axLabel PackNatural 3
  list <- listStoreNew []
  tree <- treeViewNewWithModel list
  treeViewSetHeadersVisible tree True
  col <- treeViewColumnNew
  renderer <- cellRendererTextNew
  cellLayoutPackStart col renderer True
  cellLayoutSetAttributes col renderer list $
    \row -> [cellText := (render row)]
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
  return (AA addAxBtn editAxBtn removeAxBtn list treeSel)


--------------------------------------------------------------------------------

data TheoremEntryArea = TEA
  { eName :: Entry
  , eAxioms :: Entry
  , eFrom :: Entry
  , eTo :: Entry
  , btnGo :: Button
  , btnLoad :: Button
  , btnExport :: Button
  }

theoremEntryArea :: VBox -> IO TheoremEntryArea
theoremEntryArea vbox = do
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
  return (TEA teName teAxioms teFrom teTo teBtn openBtn exportBtn)

packLabel box str = do
  l <- labelNew (Just str)
  miscSetAlignment l 0 0
  boxPackStart box l PackNatural 3
