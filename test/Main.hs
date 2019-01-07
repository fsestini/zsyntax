import Zsyntax
import qualified Otter as O
import System.Exit (exitFailure)
import qualified Data.Set as S (fromList)
import qualified Data.MultiSet as M
import Data.List.NonEmpty (fromList)
import Zsyntax.ReactionList

type Atom = BioFormula String

main :: IO ()
main = checkSequent goal

checkSequent :: Sequent Atom -> IO ()
checkSequent g =
  case O.extractResults 2000 (fst $ search (toLabelledGoal g)) of
    O.AllResults _ -> putStrLn "test passed."
    O.NoResults _  -> putStrLn "test failed." >> exitFailure

ax :: Ord a => [a] -> [a] -> [a] -> Axiom (BioFormula a)
ax xs ys rl =
  axiom (fromList $ fmap BioAtom xs)
        (justCS $ fromCSCtxts [CSC SupersetClosed
                                (M.fromList (fmap BioAtom rl))])
        (fromList $ fmap BioAtom ys)

goal :: Sequent Atom
goal = SQ (S.fromList axioms) (M.fromList from) to
  where
    axioms :: [Axiom Atom]
    axioms =
      [ ax ["ICL"] ["MUS81"] mempty
      , ax ["MUS81", "FANCD21"] ["FAN1"] mempty
      , ax ["FANCM", "ATR"] ["FAcore"] ["CHKREC"]
      , ax ["FANCM", "ATM"] ["FAcore"] ["CHKREC"]
      , ax ["FAcore", "ATM"] ["FANCD21"] ["USP1"]
      , ax ["FAcore", "ATR"] ["FANCD21"] ["USP1"]
      , ax ["FAcore", "H2AX", "DSB"] ["FANCD21"] ["USP1"]
      , ax ["ICL"] ["FANCM"] ["CHKREC"]
      , ax ["FAN1"] ["DSB"] ["HRR", "NHEJ"]
      , ax ["XPF"] ["DBS"] ["HRR", "NHEJ"]
      , ax ["MUS81", "FAN1"] ["ADD"] ["PCNATLS"]
      , ax ["ATM"] ["ATM", "ATM"] mempty
      , ax ["ICL"] ["ICL", "ICL"] mempty
      ]
    from :: [Formula Atom]
    from = [atom (BioAtom "ICL"), atom (BioAtom "ATM")]
    to :: Formula Atom
    to = conj (atom (BioAtom "DSB")) (atom (BioAtom "ADD"))

