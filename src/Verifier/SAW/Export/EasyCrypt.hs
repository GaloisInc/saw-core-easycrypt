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

import Debug.Trace

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
                  [EC.Decl]
                  (Either (TranslationError Term))
                  a
  }
  deriving (Applicative, Functor, Monad, MonadWriter [EC.Decl])

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
    PairLeft t    -> EC.TupleProject <$> transFn t <*> pure 1
    PairRight t   -> EC.TupleProject <$> transFn t <*> pure 2
    EmptyValue    -> pure $ EC.Record []
    EmptyType     -> notExpr
    FieldValue fname fvalue rest -> do fname' <- asString fname
                                       fvalue' <- transFn fvalue
                                       recr <- transFn rest
                                       case mergeRecordFields (EC.Record [EC.RecordField fname' fvalue']) recr of
                                         Just record -> return record
                                         Nothing     -> badTerm
    FieldType _ _ _    -> notExpr
    RecordSelector record field -> do field' <- asString field
                                      (flip EC.RecordProject field') <$> transFn record
    CtorApp i []       -> EC.ModVar <$> pure (translateIdent i)
    CtorApp ctorName args -> EC.App <$> flatTermFToExpr transFn (CtorApp ctorName [])
                                    <*> mapM transFn args
    DataTypeApp _ _ -> notExpr
    Sort _ -> notExpr
    NatLit i -> EC.IntLit <$> pure i
    ArrayValue _ _ -> notSupported
    FloatLit _     -> notSupported
    DoubleLit _    -> notSupported
    StringLit _    -> notSupported
    ExtCns (EC _ _ _) -> notSupported
  where
    notExpr = throwError $ NotExpr errorTerm
    notSupported = throwError $ NotSupported errorTerm
    badTerm = throwError $ BadTerm errorTerm
    errorTerm = Unshared $ FTermF tf
    asString (asFTermF -> Just (StringLit s)) = pure s
    asString _ = badTerm
    mergeRecordFields :: EC.Expr -> EC.Expr -> Maybe EC.Expr
    mergeRecordFields (EC.Record fs1) (EC.Record fs2) = Just $ EC.Record $ fs1 ++ fs2
    mergeRecordFields _ _ = Nothing

flatTermFToType ::
  (Term -> ECTrans EC.Type) ->
  FlatTermF Term ->
  ECTrans EC.Type
flatTermFToType transFn tf =
  case tf of
    GlobalDef i   -> EC.TyApp <$> pure (translateIdent i) <*> pure []
    UnitValue     -> notType
    UnitType      -> EC.TyApp <$> pure "unit" <*> pure []
    PairValue _ _ -> notType
    PairType x y  -> EC.TupleTy <$> traverse transFn [x, y]
    PairLeft _    -> notType
    PairRight _   -> notType
    EmptyValue         -> notType
    EmptyType          -> pure $ EC.TupleTy []
    FieldValue _ _ _   -> notType
    -- record types in EasyCrypt can only be used as named types, so
    -- we need to construct and declare the corresponding record type
    -- first
    FieldType _fname _ftype _rest -> trace "FieldType" notSupported
      -- do _fname' <- asString fname
      --    _ftype' <- transFn ftype
      --    _rtype <- transFn rest
    RecordSelector _ _ -> notType
    CtorApp _ _      -> notType
    DataTypeApp i args ->
      EC.TyApp <$> pure (translateIdent i) <*> traverse transFn args'
        where args' = filterArgs i args
    Sort _ -> notType
    NatLit _ -> notType
    ArrayValue _ _ -> notType
    FloatLit _  -> notType
    DoubleLit _ -> notType
    StringLit _ -> notType
    ExtCns (EC _ _ _) -> notType
  where
    notType = throwError $ NotType errorTerm
    notSupported = throwError $ NotSupported errorTerm
    -- badTerm = throwError $ BadTerm errorTerm
    errorTerm = Unshared $ FTermF tf    
    -- asString (asFTermF -> Just (StringLit s)) = pure s
    -- asString _ = badTerm
    
translateType :: [String] -> Term -> ECTrans EC.Type
translateType env t =
  case t of
    (asFTermF -> Just tf) -> flatTermFToType (translateType env) tf
    (asPi -> Just (_, ty, body)) ->
      EC.FunTy <$> translateType env ty <*> translateType env body
    (asApp -> Just _tf) -> do
      let (_f, _args) = asApplyAll t
      notSupported
      -- (tyn, args') <- case f of
      --                  (asGlobalDef -> Just i) -> (i, filterArgs i args)
      --                  _ -> notSupported
      -- EC.TyApp <$> tyn <*> traverse (translateTerm env) args'
    _ -> trace "translateType fallthrough" notSupported
  where
    notSupported = throwError $ NotSupported t

translateTerm :: [String] -> Term -> ECTrans EC.Expr
translateTerm env t =
  case t of
    (asFTermF -> Just tf)  -> flatTermFToExpr (translateTerm env) tf
    (asLambda -> Just _) -> do
      tys <- mapM (translateType env . snd) args
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
        EC.Binding EC.Lambda args b' -> tell [EC.OpDecl n args b']
        _ -> tell [EC.OpDecl n [] b]
      EC.ModVar <$> pure n
    _ -> trace "translateTerm fallthrough" notSupported
  where
    notSupported = throwError $ NotSupported t

translateTermDoc :: Term -> Either (TranslationError Term) Doc
translateTermDoc t = do
  (expr, decls) <- runWriterT $ runECTrans $ translateTerm [] t
  return $ (vcat (map ppDecl decls)) <$$> ppExpr expr
