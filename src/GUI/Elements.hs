module GUI.Elements where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Layout.HBox
import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, writeIORef, readIORef)
import Control.Monad (forM_)
import Control.Monad.Free (foldFree)
import Text.Parsec
import Checking.ReactLists.Sets
import qualified TypeClasses as T
import qualified Data.List.NonEmpty as NE

import GUI.Command --(ThrmName(..), CtrlArea(..), FrmlArea(..), aggregate1')

--------------------------------------------------------------------------------

data AxDiaContent = ADC
  { name :: ThrmName
  , from :: AxArea
  , to :: AxArea
  , ctrl :: CtrlArea
  }

parseAggregate = parse (aggregate1' <* eof) ""
parseCtxt = parse (neCtxt <* eof) ""

ctrlListView :: VBox -> IO (ListStore (CtrlSetCtxt BioAtoms))
ctrlListView vbox = do
  list <- listStoreNew []
  tree <- treeViewNewWithModel list
  treeViewSetHeadersVisible tree True
  col <- treeViewColumnNew
  renderer <- cellRendererTextNew
  cellLayoutPackStart col renderer True
  cellLayoutSetAttributes col renderer list $
     \row -> [cellText := show row]
  _ <- treeViewAppendColumn tree col
  treeViewColumnSetTitle col "Control context"
  boxPackStart vbox tree PackGrow 0
  return list

ctrlDialog :: IO (Maybe (CtrlSetCtxt BioAtoms))
ctrlDialog = do
  dia <- dialogNew
  set dia [windowTitle := "Add control context..."]
  dialogAddButton dia stockApply ResponseApply
  dialogAddButton dia stockCancel ResponseCancel
  upbox <- dialogGetUpper dia
  regularBtn <- radioButtonNewWithLabel "Regular"
  boxPackStart upbox regularBtn PackNatural 0
  supsetBtn <- radioButtonNewWithLabelFromWidget regularBtn "Superset-closed"
  boxPackStart upbox supsetBtn PackNatural 0
  toggleButtonSetActive regularBtn True
  e <- titledEntry upbox "Context: "
  widgetShowAll upbox
  answer <- dialogRun dia
  result <-
    if answer == ResponseApply
      then do
        txt <- entryGetText e :: IO String
        flip (either (const (return Nothing))) (parseCtxt txt) $ \ctxt -> do
          state <- toggleButtonGetActive regularBtn
          if state
             then return (Just (Regular ctxt))
             else return (Just (SupsetClosed ctxt))
      else return Nothing
  widgetDestroy dia
  return result

axiomsDialog :: String -> (Maybe AxDiaContent) -> IO (Maybe AxDiaContent)
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
  entrySetText axNmE (maybe "" (unTN . name) content)
  axFromE <- titledEntry upbox "Start aggregate: "
  entrySetText axFromE (maybe "" (T.pretty . from) content)
  axToE <- titledEntry upbox "Result aggregate: "
  entrySetText axToE (maybe "" (T.pretty . to) content)
  list <- ctrlListView upbox
  btnAddCtrl <- buttonNewWithLabel "Add control context"
  boxPackStart upbox btnAddCtrl PackNatural 0
  onClicked btnAddCtrl $ do
    res <- ctrlDialog
    case res of
      Just ctxt -> listStoreAppend list ctxt >> return ()
      Nothing -> return ()
  widgetShowAll upbox
  answer <- dialogRun dia
  result <-
    if answer == ResponseApply
      then do
        nmTxt <- entryGetText axNmE :: IO String
        fromTxt <- entryGetText axFromE :: IO String
        toTxt <- entryGetText axToE :: IO String
        ctrls <- listStoreToList list
        let eee = do
              from <- parseAggregate fromTxt
              to <- parseAggregate toTxt
              return (from, to)
        flip (either (const (return Nothing))) eee $ \(from, to) ->
          return . Just $
          ADC (TN nmTxt) (AA from) (AA to) (CA (fromFoldableCtxts ctrls))
      else return Nothing
  widgetDestroy dia
  return result

titledEntry :: VBox -> String -> IO Entry
titledEntry vbox str = do
  l <- labelNew (Just str)
  hb <- hBoxNew False 0
  boxPackStart hb l PackNatural 5
  entry <- entryNew
  boxPackStart hb entry PackGrow 5
  boxPackStart vbox hb PackNatural 0
  return entry

--------------------------------------------------------------------------------

addSep :: VBox -> IO ()
addSep vbox = hSeparatorNew >>= \s -> boxPackStart vbox s PackNatural 10

buildListView
  :: (BoxClass box)
  => box
  -> NE.NonEmpty (String, t -> String)
  -> Packing
  -> IO (TreeView, ListStore t)
buildListView vbox cols packing = do
  list <- listStoreNew []
  tree <- treeViewNewWithModel list
  treeViewSetHeadersVisible tree True
  forM_ cols $ \(title, render) -> do
    col <- treeViewColumnNew
    renderer <- cellRendererTextNew
    cellLayoutPackStart col renderer True
    cellLayoutSetAttributes col renderer list $
      \row -> [cellText := (render row)]
    _ <- treeViewAppendColumn tree col
    treeViewColumnSetTitle col title
  boxPackStart vbox tree packing 0
  return (tree, list)

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

theoremArea :: VBox -> NE.NonEmpty (String, t -> String) -> IO (ListStore t)
theoremArea vbox renders = do
  thLabel <- labelNew (Just "Theorems:")
  miscSetAlignment thLabel 0 0
  boxPackStart vbox thLabel PackNatural 3
  (_,thList) <- buildListView vbox renders PackGrow
  return thList

--------------------------------------------------------------------------------

data AxiomsArea t = GUIAA
  { btnAddAxiom :: Button
  , btnChangeAxiom :: Button
  , btnRemoveAxiom :: Button
  , storeAxioms :: ListStore t
  , treeSelAxioms :: TreeSelection
  }

axiomsArea :: VBox -> NE.NonEmpty (String, t -> String) -> IO (AxiomsArea t)
axiomsArea vbox cols = do
  axLabel <- labelNew (Just "Axioms:")
  miscSetAlignment axLabel 0 0
  boxPackStart vbox axLabel PackNatural 3

  axHb <- hBoxNew False 10
  (tree, list) <- buildListView axHb cols PackGrow
  treeSel <- treeViewGetSelection tree
  treeSelectionSetMode treeSel SelectionSingle

  axBtnsVb <- vBoxNew False 0
  addAxBtn <- buttonNewWithLabel "Add axiom"
  boxPackStart axBtnsVb addAxBtn PackNatural 0
  editAxBtn <- buttonNewWithLabel "Edit axiom"
  boxPackStart axBtnsVb editAxBtn PackNatural 0
  removeAxBtn <- buttonNewWithLabel "Remove axiom"
  boxPackStart axBtnsVb removeAxBtn PackNatural 0
  boxPackStart axHb axBtnsVb PackNatural 0
  boxPackStart vbox axHb PackGrow 0
  return (GUIAA addAxBtn editAxBtn removeAxBtn list treeSel)


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
