module GUI.Elements where

import Safe (headMay)
import Utils (discardResP, on', maybe')
import Graphics.UI.Gtk
import Graphics.UI.Gtk.Layout.HBox
import Control.Monad (join)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, writeIORef, readIORef)
import Control.Monad (forM_, liftM2)
import Control.Monad.Free (foldFree)
import Text.Parsec
import Checking.ReactLists.Sets
import qualified TypeClasses as T
import qualified Data.List.NonEmpty as NE
import Control.Newtype

import GUI.Command

--------------------------------------------------------------------------------

data AxDiaContent = ADC
  { adcName :: Name
  , adcRepr :: AxRepr
  }

parseAggregate = parse (aggregate1' <* eof) ""
parseCtxt = parse (neCtxt <* eof) ""

ctrlListView :: VBox -> IO (TreeSelection, ListStore (CtrlSetCtxt BioAtoms))
ctrlListView vbox = do
  (tree, list) <-
    buildListView vbox (("Control context", shower) NE.:| []) PackGrow
  sel <- treeViewGetSelection tree
  return (sel, list)
  where
    shower (Regular ctxt) = "regular " ++ asFoldable T.prettys ctxt
    shower (SupsetClosed ctxt) = "superset-closed " ++ asFoldable T.prettys ctxt

ctrlDialog
  :: WindowClass w
  => w -> Maybe (CtrlSetCtxt BioAtoms) -> IO (Maybe (CtrlSetCtxt BioAtoms))
ctrlDialog p ctxt = do
  dia <- dialogNew
  windowSetTransientFor dia p
  set dia [windowTitle := "Add control context..."]
  dialogAddButton dia stockApply ResponseApply
  dialogAddButton dia stockCancel ResponseCancel
  upbox <- dialogGetUpper dia
  regularBtn <- radioButtonNewWithLabel "Strict"
  boxPackStart upbox regularBtn PackNatural 0
  supsetBtn <- radioButtonNewWithLabelFromWidget regularBtn "Superset-closed"
  boxPackStart upbox supsetBtn PackNatural 0
  toggleButtonSetActive supsetBtn True
  e <- titledEntry upbox "Context: "
  maybe' ctxt (return ()) $ \x ->
    case x of
      Regular c ->
        toggleButtonSetActive regularBtn True >>
        entrySetText e (asFoldable T.prettys c)
      SupsetClosed c ->
        toggleButtonSetActive supsetBtn True >>
        entrySetText e (asFoldable T.prettys c)
  widgetShowAll upbox
  answer <- dialogRun dia
  result <-
    if answer == ResponseApply
      then do
        txt <- entryGetText e :: IO String
        flip (either (discardResP . errorDiagShow p)) (parseCtxt txt) $ \ctxt -> do
          state <- toggleButtonGetActive regularBtn
          if state
            then return (Just (Regular ctxt))
            else return (Just (SupsetClosed ctxt))
      else return Nothing
  widgetDestroy dia
  return result

--------------------------------------------------------------------------------

selected :: ListStore t -> TreeSelection -> IO [(Int, t)]
selected store treeSel =
  treeSelectionGetSelectedRows treeSel >>=
  mapM (on' (liftM2 (,)) (return) (listStoreGetValue store)) .
  fmap (maybe (error "fatal error in ListStore selector") id) . fmap headMay

--------------------------------------------------------------------------------

axiomsDialog
  :: WindowClass w
  => w -> String -> Maybe AxDiaContent -> IO (Maybe AxDiaContent)
axiomsDialog p title content = do
  dia <- dialogNew
  windowSetTransientFor dia p
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
  entrySetText axNmE (maybe "" (unpack . adcName) content)
  axFromE <- titledEntry upbox "Start aggregate: "
  entrySetText axFromE (maybe "" (exportAggregate . from . adcRepr) content)
  axToE <- titledEntry upbox "Result aggregate: "
  entrySetText axToE (maybe "" (exportAggregate . to . adcRepr) content)
  (sel, list) <- ctrlListView upbox
  forM_ (maybe [] (toCtxtList . ctrl . adcRepr) content) (listStoreAppend list)
  btnAddCtrl <- buttonNewWithLabel "Add control context"
  btnEditCtrl <- buttonNewWithLabel "Edit control context"
  btnRemoveCtrl <- buttonNewWithLabel "Remove control context"
  h <- hBoxNew True 0
  boxPackStart h btnAddCtrl PackGrow 0
  boxPackStart h btnEditCtrl PackGrow 0
  boxPackStart h btnRemoveCtrl PackGrow 0
  boxPackStart upbox h PackNatural 0
  onClicked btnAddCtrl $ do
    res <- ctrlDialog dia Nothing
    case res of
      Just ctxt -> listStoreAppend list ctxt >> return ()
      Nothing -> return ()
  onClicked btnEditCtrl $
    fmap headMay (selected list sel) >>= maybe (return ()) (\(i,c) ->
      ctrlDialog dia (Just c)
      >>= maybe (return ()) (listStoreSetValue list i))
  onClicked btnRemoveCtrl $
    fmap headMay (selected list sel) >>= maybe (return ()) (\(i,_) ->
      listStoreRemove list i)
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
        flip (either (discardResP . errorDiagShow p . show)) eee $ \(from, to) ->
          return . Just $
          ADC (NM nmTxt) (AR (Aggr from) (fromFoldableCtxts ctrls) (Aggr to))
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

askReplaceThrm :: Window -> Name -> IO ReplaceAnswer
askReplaceThrm p nm@(NM name) = do
  dia <- dialogNew
  windowSetTransientFor dia p
  windowSetModal dia True
  dialogAddButton dia stockYes ResponseYes
  dialogAddButton dia stockNo ResponseNo
  upbox <- dialogGetUpper dia
  l <-
    labelNew
      (Just ("A theorem named '" ++ name ++ "' already exists. Replace?"))
  boxPackStart upbox l PackNatural 0
  widgetShowAll upbox
  answer <- dialogRun dia
  let res =
        case answer of
          ResponseYes -> Yes
          _ -> No
  widgetDestroy dia
  return res

errorDiag :: WindowClass w => w -> String -> IO ()
errorDiag p msg = do
  dia <- dialogNew
  windowSetTransientFor dia p
  windowSetModal dia True
  dialogAddButton dia stockOk ResponseOk
  upbox <- dialogGetUpper dia
  l <- labelNew (Just msg)
  boxPackStart upbox l PackNatural 0
  widgetShowAll upbox
  _ <- dialogRun dia
  widgetDestroy dia

errorDiagShow :: (WindowClass w, Show a) => w -> a -> IO ()
errorDiagShow p = errorDiag p . show

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

data TheoremsArea t = TA
  { btnRefreshThrms :: Button
  , btnCopyThrm :: Button
  , btnRemoveThrm :: Button
  , storeThrms :: ListStore t
  , treeSelThrms :: TreeSelection
  }

theoremArea :: VBox -> NE.NonEmpty (String, t -> String) -> IO (TheoremsArea t)
theoremArea vbox renders = do
  thLabel <- labelNew (Just "Theorems:")
  miscSetAlignment thLabel 0 0
  boxPackStart vbox thLabel PackNatural 3

  h <- hBoxNew False 10
  (tree, list) <- buildListView h renders PackGrow
  treeSel <- treeViewGetSelection tree

  btns <- vBoxNew False 0
  btnRefresh <- buttonNewWithLabel "Refresh all"
  boxPackStart btns btnRefresh PackNatural 0
  btnCopy <- buttonNewWithLabel "Copy to area"
  boxPackStart btns btnCopy PackNatural 0
  btnRem <- buttonNewWithLabel "Remove theorem"
  boxPackStart btns btnRem PackNatural 0
  boxPackStart h btns PackNatural 0
  boxPackStart vbox h PackGrow 0
  return (TA btnRefresh btnCopy btnRem list treeSel)

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
  , btnClear :: Button
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
  clearBtn <- buttonNewWithLabel "Clear"
  boxPackStart hb teBtn PackNatural 3
  boxPackStart hb loadBtn PackNatural 3
  boxPackStart hb openBtn PackNatural 3
  boxPackStart hb exportBtn PackNatural 3
  boxPackStart hb clearBtn PackNatural 3

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
        loadBtn openBtn exportBtn clearBtn

packLabel box str = do
  l <- labelNew (Just str)
  miscSetAlignment l 0 0
  boxPackStart box l PackNatural 3