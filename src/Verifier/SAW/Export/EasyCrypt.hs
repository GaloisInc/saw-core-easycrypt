{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Export.EasyCrypt
Copyright   : Galois, Inc. 2017
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Verifier.SAW.Export.EasyCrypt where

import Control.Monad.Except
import Control.Monad.Writer
import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.EasyCrypt.AST as EC
import Data.EasyCrypt.Pretty
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor

data TranslationError a
  = NotSupported a
  | NotExpr a
  | NotType a
  | LocalVarOutOfBounds a
  | BadTerm a
  deriving (Show)

newtype ECTrans a =
  ECTrans {
    runECTrans :: WriterT
                  [EC.Def]
                  (Either (TranslationError Term))
                  a
  }
  deriving (Applicative, Functor, Monad, MonadWriter [EC.Def])

instance MonadError (TranslationError Term) ECTrans where
    throwError e = ECTrans $ lift $ throwError e
    catchError (ECTrans a) h = ECTrans $ catchError a $ runECTrans . h

zipFilter :: [Bool] -> [a] -> [a]
zipFilter bs = map snd . filter fst . zip bs

showFTermF :: FlatTermF Term -> String
showFTermF = show . Unshared . FTermF

globalArgsMap :: Map.Map Ident [Bool]
globalArgsMap = Map.fromList
  [ ("Prelude.append", [False, False, False, True, True])
  , ("Prelude.take", [False, True, False, True])
  , ("Prelude.drop", [False, False, True, True])
  , ("Prelude.Vec", [False, True])
  ]

filterArgs :: Ident -> [a] -> [a]
filterArgs i = maybe id zipFilter (Map.lookup i globalArgsMap)

translateIdent :: Ident -> EC.Ident
translateIdent i =
  case i of
    "Prelude.Bool" -> "bool"
    "Prelude.False" -> "false"
    "Prelude.True" -> "true"
    "Prelude.Nat" -> "int"
    "Prelude.Vec" -> "list"
    "Prelude.append" -> "(++)"
    "Prelude.take" -> "take"
    "Prelude.drop" -> "drop"
    "Prelude.zip" -> "zip"
    "Prelude.zipWith" -> "zipWith"
    _ -> show i

flatTermFToExpr ::
  (Term -> ECTrans EC.Expr) ->
  FlatTermF Term ->
  ECTrans EC.Expr
flatTermFToExpr transFn tf =
  case tf of
    GlobalDef i   -> EC.ModVar <$> pure (translateIdent i)
    UnitValue     -> EC.Tuple <$> pure [] -- TODO: hack
    UnitType      -> notExpr
    PairValue x y -> EC.Tuple <$> traverse transFn [x, y]
    PairType _ _  -> notExpr
    PairLeft t    -> EC.Project <$> transFn t <*> pure 1
    PairRight t   -> EC.Project <$> transFn t <*> pure 2
    EmptyValue         -> notSupported
    EmptyType          -> notExpr
    FieldValue _ _ _   -> notSupported
    FieldType _ _ _    -> notExpr
    RecordSelector _ _ -> notSupported
    CtorApp i []       -> EC.ModVar <$> pure (translateIdent i)
    CtorApp _ _        -> notSupported
    DataTypeApp _ _ -> notExpr
    Sort _ -> notExpr
    NatLit i -> EC.IntLit <$> pure i
    ArrayValue _ _ -> notSupported
    FloatLit _  -> notSupported
    DoubleLit _ -> notSupported
    StringLit _ -> notSupported
    ExtCns (EC _ _ _) -> notSupported
  where
    notExpr = throwError $ NotExpr $ Unshared $ FTermF tf
    notSupported = throwError $ NotSupported $ Unshared $ FTermF tf

flatTermFToType ::
  (Term -> ECTrans EC.Type) ->
  FlatTermF Term ->
  ECTrans EC.Type
flatTermFToType transFn tf =
  case tf of
    GlobalDef i   -> EC.TyConstr <$> pure (translateIdent i) <*> pure []
    UnitValue     -> notType
    UnitType      -> EC.TyConstr <$> pure "unit" <*> pure []
    PairValue _ _ -> notType
    PairType x y  -> EC.TupleTy <$> traverse transFn [x, y]
    PairLeft _    -> notType
    PairRight _   -> notType
    EmptyValue         -> notType
    EmptyType          -> pure $ EC.TupleTy []
    FieldValue _ _ _   -> notType
    FieldType _ _ _    -> notSupported
    RecordSelector _ _ -> notType
    CtorApp _ _      -> notType
    DataTypeApp i args ->
      EC.TyConstr <$> pure (translateIdent i) <*> traverse transFn args'
        where args' = filterArgs i args
    Sort _ -> notType
    NatLit _ -> notType
    ArrayValue _ _ -> notType
    FloatLit _  -> notType
    DoubleLit _ -> notType
    StringLit _ -> notType
    ExtCns (EC _ _ _) -> notType
  where
    notType = throwError $ NotType $ Unshared $ FTermF tf
    notSupported = throwError $ NotSupported $ Unshared $ FTermF tf

translateType :: Term -> ECTrans EC.Type
translateType t =
  case t of
    (asFTermF -> Just tf) -> flatTermFToType translateType tf
    (asPi -> Just (_, ty, body)) ->
      EC.FunTy <$> translateType ty <*> translateType body
    _ -> notSupported
  where
    notSupported = throwError $ NotSupported t

translateTerm :: [String] -> Term -> ECTrans EC.Expr
translateTerm env t =
  case t of
    (asFTermF -> Just tf)  -> flatTermFToExpr (translateTerm env) tf
    (asLambda -> Just _) -> do
      tys <- mapM (translateType . snd) args
      EC.Binding EC.Lambda <$> pure (zip argNames (map Just tys))
                           <*> translateTerm (argNames ++ env) e
        where
          (args, e) = asLambdaList t
          argNames = map fst args
    (asApp -> Just _) -> do
      let (f, args) = asApplyAll t
          args' = case f of
                    (asGlobalDef -> Just i) -> filterArgs i args
                    _ -> args
      EC.App <$> translateTerm env f
             <*> traverse (translateTerm env) args'
    (asLocalVar -> Just n)
      | n < length env -> EC.LocalVar <$> pure (env !! n)
      | otherwise -> throwError $ LocalVarOutOfBounds t
    (unwrapTermF -> Constant n body _) -> do
      b <- translateTerm env body
      case b of
        EC.Binding EC.Lambda args b' -> tell [EC.Def n args b']
        _ -> tell [EC.Def n [] b]
      EC.ModVar <$> pure n
    _ -> notSupported
  where
    notSupported = throwError $ NotSupported t

translateTermDoc :: Term -> Either (TranslationError Term) Doc
translateTermDoc t = do
  (expr, defs) <- runWriterT $ runECTrans $ translateTerm [] t
  return $ (vcat (map ppDef defs)) <$$> ppExpr expr
