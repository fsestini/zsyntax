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
  , repr :: AxRepr
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
     \row -> [cellText := shower row]
  _ <- treeViewAppendColumn tree col
  treeViewColumnSetTitle col "Control context"
  boxPackStart vbox tree PackGrow 0
  return list
  where
    shower (Regular ctxt) = "regular " ++ asFoldable T.prettys ctxt
    shower (SupsetClosed ctxt) = "superset-closed " ++ asFoldable T.prettys ctxt

ctrlDialog :: WindowClass w => w -> IO (Maybe (CtrlSetCtxt BioAtoms))
ctrlDialog parent = do
  dia <- dialogNew
  windowSetTransientFor dia parent
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

axiomsDialog
  :: WindowClass w
  => w -> String -> (Maybe AxDiaContent) -> IO (Maybe AxDiaContent)
axiomsDialog parent title content = do
  dia <- dialogNew
  windowSetTransientFor dia parent
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
  entrySetText axFromE (maybe "" (T.pretty . from . repr) content)
  axToE <- titledEntry upbox "Result aggregate: "
  entrySetText axToE (maybe "" (T.pretty . to . repr) content)
  list <- ctrlListView upbox
  forM_ (maybe [] (toCtxtList . ctrl . repr) content) (listStoreAppend list)
  btnAddCtrl <- buttonNewWithLabel "Add control context"
  boxPackStart upbox btnAddCtrl PackNatural 0
  onClicked btnAddCtrl $ do
    res <- ctrlDialog dia
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
          ADC (TN nmTxt) (AR (Aggr from) (fromFoldableCtxts ctrls) (Aggr to))
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
  scroll <- scrolledWindowNew Nothing Nothing

  list <- listStoreNew []
  tree <- treeViewNewWithModel list

  sel <- treeViewGetSelection tree
  treeSelectionSetMode sel SelectionMultiple

  treeViewSetHeadersVisible tree True
  forM_ cols $ \(title, render) -> do
    col <- treeViewColumnNew
    renderer <- cellRendererTextNew
    cellLayoutPackStart col renderer True
    cellLayoutSetAttributes col renderer list $
      \row -> [cellText := (render row)]
    _ <- treeViewAppendColumn tree col
    treeViewColumnSetTitle col title

  scrolledWindowAddWithViewport scroll tree
  boxPackStart vbox scroll packing 0
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
  , rbSome :: RadioButton
  , rbAll :: RadioButton
  , chkRefine :: CheckButton
  , eFrom :: Entry
  , eTo :: Entry
  , btnGo :: Button
  , btnLoad :: Button
  , btnOpen :: Button
  , btnExport :: Button
  }

theoremEntryArea :: VBox -> IO TheoremEntryArea
theoremEntryArea vbox = do
  nameHb <- hBoxNew False 0
  l1 <- labelNew (Just "Name:   ")
  teName <- entryNew
  boxPackStart nameHb l1 PackNatural 0
  boxPackStart nameHb teName PackGrow 0
  boxPackStart vbox nameHb PackNatural 3
  -- miscSetAlignment l1 1 1

  hb <- hBoxNew False 0
  teBtn <- buttonNewWithLabel "Go"
  loadBtn <- buttonNewWithLabel "Load file..."
  openBtn <- buttonNewWithLabel "Open file..."
  exportBtn <- buttonNewWithLabel "Export..."
  boxPackStart hb teBtn PackNatural 3
  boxPackStart hb loadBtn PackNatural 3
  boxPackStart hb openBtn PackNatural 3
  boxPackStart hb exportBtn PackNatural 3

  testAxHb <- hBoxNew False 0
  testrbAx <- radioButtonNewWithLabel "Axioms: "
  boxPackStart testAxHb testrbAx PackNatural 3
  teAxioms <- entryNew
  boxPackStart testAxHb teAxioms PackGrow 3
  spaceL <- labelNew (Just "    ")
  boxPackStart testAxHb spaceL PackNatural 3
  testrbAll <- radioButtonNewWithLabelFromWidget testrbAx "Use all"
  boxPackStart testAxHb testrbAll PackNatural 3
  chkRefine <- checkButtonNewWithLabel "Refine"
  boxPackStart testAxHb chkRefine PackNatural 3
  boxPackStart vbox testAxHb PackNatural 3

  testhb <- hBoxNew False 0
  testl1 <- labelNew (Just "Start aggr.: ")
  testl2 <- labelNew (Just "End aggr.: ")
  teFrom <- entryNew
  teTo <- entryNew
  boxPackStart testhb testl1 PackNatural 5
  boxPackStart testhb teFrom PackGrow 5
  boxPackStart testhb testl2 PackNatural 5
  boxPackStart testhb teTo PackGrow 5

  boxPackStart vbox testhb PackNatural 3

  boxPackStart vbox hb PackNatural 7
  return $
    TEA teName teAxioms testrbAx testrbAll chkRefine teFrom teTo teBtn
        loadBtn openBtn exportBtn

packLabel box str = do
  l <- labelNew (Just str)
  miscSetAlignment l 0 0
  boxPackStart box l PackNatural 3
