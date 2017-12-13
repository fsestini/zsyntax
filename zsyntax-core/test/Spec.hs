{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import Test.QuickCheck
import qualified Data.List.NonEmpty as NE
import LinearContext.PosInt
import LinearContext
import Data.Foldable
import Data.List
import qualified TypeClasses as T
import Test.QuickCheck.Function
import Data.Maybe
import Checking.ReactLists.RList
import Checking.ReactLists.Sets
import LFormula

main :: IO ()
main = do
  quickCheck prop_posIntIsPos
  quickCheck prop_emptyLC
  quickCheck prop_listInvarianceLC
  quickCheck prop_mergeLC
  quickCheck prop_subCtxtLC
  quickCheck prop_subcNotInLC
  quickCheck prop_singletonLC

  quickCheck prop_listInvarianceNELC
  quickCheck prop_mergeNELC
  quickCheck prop_subCtxtNELC
  quickCheck prop_subcNotInNELC
  quickCheck prop_singletonNELC
  quickCheck prop_NELCtoLC
  quickCheck prop_matchSubc
  quickCheck prop_matchReflexive

  quickCheck (prop_EmptyBaseRespAll @Int)

instance Arbitrary PosInt where
  arbitrary = do
    n <- arbitrary
    let n' = if n >= 0
                then n
                else -n
    return $ chain piOne !! n'
    where
      chain x = x : chain (piSucc x)

prop_posIntIsPos :: PosInt -> Bool
prop_posIntIsPos pi = toInt pi > 0

--------------------------------------------------------------------------------

countElem :: Eq a => a -> LinearCtxt a -> Int
countElem x lc = maybe 0 id $ lookup x (fmap (\l@ (x:_) -> (x,length l)) $ group (toList lc))

prop_emptyLC :: Bool
prop_emptyLC = (length . toList) (mempty :: LinearCtxt Int) == 0

prop_listInvarianceLC :: [Int] -> Bool
prop_listInvarianceLC lst =
  sort (toList (fromFoldable lst :: LinearCtxt Int)) == sort lst

btwZeroTen :: Gen Int
btwZeroTen = suchThat arbitrary (\n -> 0 <= n && n <= 10)

instance Arbitrary (LinearCtxt Int) where
  arbitrary = do
    list1 <- listOf btwZeroTen
    return $ fromFoldable list1

prop_mergeLC :: LinearCtxt Int -> LinearCtxt Int -> Bool
prop_mergeLC lc1 lc2 =
  sort (toList (lc1 `mappend` lc2)) == sort ((toList lc1 ++ toList lc2))

prop_subCtxtLC :: LinearCtxt Int -> LinearCtxt Int -> Bool
prop_subCtxtLC lc1 lc2 = subCtxtOf lc1 (lc1 <> lc2)

prop_subcNotInLC :: LinearCtxt Int -> LinearCtxt Int -> Bool
prop_subcNotInLC lc1 lc2 =
  not (subCtxtOf lc1 lc2) ==
  (or $ fmap (\x -> countElem x lc1 > countElem x lc2) $ nub (toList lc1))

prop_singletonLC :: Int -> Bool
prop_singletonLC x = toList (singleton x :: LinearCtxt Int) == [x]

--------------------------------------------------------------------------------

instance Arbitrary (NonEmptyLinearCtxt Int) where
  arbitrary = do
    (x:xs) <- listOf1 btwZeroTen
    return $ fromNEList (x NE.:| xs)

countElemNELC :: Ord a => a -> NonEmptyLinearCtxt a -> Int
countElemNELC x = countElem x . toLC

nelcToList = toList . toNEList

prop_listInvarianceNELC :: NE.NonEmpty Int -> Bool
prop_listInvarianceNELC lst =
  sort ((toList . toNEList) (fromNEList lst :: NonEmptyLinearCtxt Int)) ==
  sort (toList lst)

prop_mergeNELC :: NonEmptyLinearCtxt Int -> NonEmptyLinearCtxt Int -> Bool
prop_mergeNELC lc1 lc2 =
  sort ((toList . toNEList) (lc1 <> lc2)) ==
  sort (((toList . toNEList) lc1 ++ (toList . toNEList) lc2))

prop_subCtxtNELC :: NonEmptyLinearCtxt Int -> NonEmptyLinearCtxt Int -> Bool
prop_subCtxtNELC lc1 lc2 = subCtxtOf lc1 (lc1 <> lc2)

prop_subcNotInNELC :: LinearCtxt Int -> LinearCtxt Int -> Bool
prop_subcNotInNELC lc1 lc2 =
  not (subCtxtOf lc1 lc2) ==
  (or $ fmap (\x -> countElem x lc1 > countElem x lc2) $ nub (toList lc1))

prop_singletonNELC :: Int -> Bool
prop_singletonNELC x = (toList . toNEList) (singleton x :: NonEmptyLinearCtxt Int) == [x]

prop_NELCtoLC :: NonEmptyLinearCtxt Int -> Bool
prop_NELCtoLC nelc = sort (nelcToList nelc) == sort (toList (toLC nelc))

prop_matchSubc :: LinearCtxt Int -> NonEmptyLinearCtxt Int -> Bool
prop_matchSubc lc nelc =
  (lc `subCtxtOf` toLC nelc) == (isJust (match lc nelc))

prop_matchPlusRes :: LinearCtxt Int -> NonEmptyLinearCtxt Int -> Bool
prop_matchPlusRes lc nelc = maybe True id $ do
  res <- match lc nelc
  return $ (lc <> res) == (toLC nelc)

prop_matchReflexive :: NonEmptyLinearCtxt Int -> Bool
prop_matchReflexive nelc =
  case match (toLC nelc) nelc of
    Nothing -> False
    Just res -> toList res == []

--------------------------------------------------------------------------------

instance Arbitrary a => Arbitrary (BioFormula a) where
  arbitrary = do
    x <- choose (True,False) :: Gen Bool
    atom <- arbitrary :: Gen a
    left <- arbitrary
    right <- arbitrary
    if x
       then return $ BioAtom atom
       else return $ BioInter left right

instance (Arbitrary a, Ord a) => Arbitrary (NonEmptyLinearCtxt (BioFormula a)) where
  arbitrary = do
    (x:xs) <- listOf1 arbitrary :: Gen [BioFormula a]
    return $ fromNEList (x NE.:| xs)


instance (Arbitrary a, Ord a) => Arbitrary (LinearCtxt (BioFormula a)) where
  arbitrary = do
    l <- listOf arbitrary :: Gen [BioFormula a]
    return $ fromFoldable l

instance (Arbitrary a, Ord a) => Arbitrary (ElemBase a) where
  arbitrary = do
    ctxt <- arbitrary
    return . EB $ ctxt

instance (Arbitrary a, Ord a) => Arbitrary (CtrlSetCtxt a) where
  arbitrary = do
    x <- choose (True,False)
    ctxt <- arbitrary :: Gen (NonEmptyLinearCtxt (BioFormula a))
    if x
       then return $ Regular ctxt
       else return $ SupsetClosed ctxt

instance (Arbitrary a, Ord a) => Arbitrary (CtrlSet a) where
  arbitrary = do
    ctxts <- listOf arbitrary :: Gen [CtrlSetCtxt a]
    return . fromFoldableCtxts $ ctxts

prop_EmptyBaseRespAll :: Ord a => CtrlSet a -> Bool
prop_EmptyBaseRespAll ctrl = respectsCtrlSet mempty ctrl
