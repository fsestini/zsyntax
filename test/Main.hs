{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Zsyntax
import qualified Otter as O
import System.Exit (exitFailure)
import qualified Data.Set as S (fromList)
import qualified Data.MultiSet as M
import Data.List.NonEmpty (fromList)
import Zsyntax.ReactionList

import Test.Hspec
import Test.QuickCheck
  (Arbitrary(..), Gen, oneof, elements, chooseInt, vectorOf, vector, getSize,
  resize)
import Data.Bool (bool)
import Data.Text (Text, pack)
import qualified Data.List.NonEmpty as NE
import Test.Hspec.QuickCheck (prop)

type Atom = BioFormula String

-- genBioFormula :: Arbitrary a => Int -> Gen (BioFormula a)
-- genBioFormula 0 = BioAtom <$> arbitrary
-- genBioFormula n = BioInter <$> genBioFormula (n - 1) <*> genBioFormula (n - 1)

instance Arbitrary a => Arbitrary (BioFormula a) where
  arbitrary = do
    n <- getSize
    x <- chooseInt (0, n)
    if x == 0
      then BioAtom <$> arbitrary
      else resize (x - 1) (BioInter <$> arbitrary <*> arbitrary)
    -- arbitrary >>=
    --   bool (BioAtom <$> arbitrary) (BioInter <$> arbitrary <*> arbitrary)

newtype BioLabel = BioLabel Text deriving newtype (Eq, Ord, Show)

instance Arbitrary BioLabel where
  arbitrary = do
    let az = elements "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    x <- az
    y <- az
    z <- az
    pure (BioLabel (pack [x, y, z]))

genAxioms :: Arbitrary a => (Int, Int) -> (Int, Int) -> Gen ([a], [Axiom a], [a])
genAxioms ns ms = do
  n <- chooseInt ns -- (5, 10)
  m <- chooseInt ms -- (10, 20)
  xs <- vectorOf m (vectorOf n (resize 5 arbitrary))
  end <- vector n
  let (start, axs) =
        foldr (\as (bs, axs) ->
                 (as, zipWith (\x y -> axiom (NE.singleton x) mempty (NE.singleton y)) as bs ++ axs))
              (end, []) xs
  pure (start, axs, end)

genSequent :: (Ord a, Arbitrary a) => (Int, Int) -> (Int, Int) -> Gen (Sequent a)
genSequent ns ms = do
  (start, axs, end) <- genAxioms ns ms
  let endFormula = foldr1 conj (map atom end)
  pure (SQ (S.fromList axs) (M.fromList (map atom start)) endFormula)

instance (Ord a, Arbitrary a) => Arbitrary (Sequent a) where
  arbitrary = genSequent (2,5) (2,5)

main :: IO ()
main = hspec $ do
  describe "test sequent" $ do
    it "checks that the goal is provable" $ do
      checkSequent goal `shouldBe` True
    prop "random tests should be provable" $
      \s -> checkSequent (s :: Sequent (BioFormula BioLabel))

checkSequent :: Ord a => Sequent a -> Bool -- IO ()
checkSequent g =
  case otterResult $ search g 5000 of -- (toLabelledGoal g)) of
    Right _ -> True -- putStrLn "test passed."
    Left _  -> False -- putStrLn "test failed." >> exitFailure

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

