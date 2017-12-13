{-# LANGUAGE TemplateHaskell #-}

module TH where

import Language.Haskell.TH

liftFun :: Name -> Name -> Q [Dec]
liftFun ctorName funName =
  return . return $
    FunD extFunName [Clause [ConP ctorName [VarP (mkName "x")]]
      (NormalB (AppE (ConE ctorName) (AppE (VarE funName) (VarE (mkName "x"))))) []]
  where
    nudeCtor = nameBase ctorName
    extFunName = mkName $ nameBase funName ++ nudeCtor

liftFuns :: Name -> [Name] -> Q [Dec]
liftFuns ctorName = fmap concat . mapM (liftFun ctorName)

liftUnifun :: Name -> Name -> Q [Dec]
liftUnifun ctorName funName =
  return . return $
    FunD extFunName [Clause [VarP (mkName "x"),
      ConP ctorName [VarP (mkName "z")]]
        (NormalB (AppE (ConE ctorName)
          ((AppE (AppE (VarE funName) (VarE (mkName "x"))) (VarE (mkName "z")))))) []]
  where
    nudeCtor = nameBase ctorName
    extFunName = mkName $ nameBase funName ++ nudeCtor

liftUnifuns :: Name -> [Name] -> Q [Dec]
liftUnifuns ctorName = fmap concat . mapM (liftFun ctorName)

liftBifun :: Name -> Name -> Q [Dec]
liftBifun ctorName funName =
  return . return $
    FunD extFunName [Clause [VarP (mkName "x"),VarP (mkName "y"),
      ConP ctorName [VarP (mkName "z")]]
        (NormalB (AppE (ConE ctorName) (AppE (AppE (AppE
          (VarE funName) (VarE (mkName "x"))) (VarE (mkName "y"))) (VarE (mkName "z"))))) []]
  where
    nudeCtor = nameBase ctorName
    extFunName = mkName $ nameBase funName ++ nudeCtor

liftBifuns :: Name -> [Name] -> Q [Dec]
liftBifuns ctorName = fmap concat . mapM (liftBifun ctorName)
