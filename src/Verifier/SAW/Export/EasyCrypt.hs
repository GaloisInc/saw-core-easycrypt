{-# LANGUAGE
  FlexibleInstances,
  GeneralizedNewtypeDeriving,
  MultiParamTypeClasses,
  OverloadedStrings,
  ViewPatterns
#-}

{- |
Module      : Verifier.SAW.Export.EasyCrypt
Copyright   : Galois, Inc. 2017
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable (TODO?)
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

data TranslationError t
  = NotSupported
  | NotExpr
  | NotType
  deriving (Show)

newtype ECTrans a =
  ECTrans {
    runECTrans :: WriterT
                  [EC.Def]
                  (Either (TranslationError Term))
                  a
  }
  deriving (Applicative, Functor, Monad)

instance MonadError (TranslationError Term) ECTrans where
    throwError e = ECTrans $ lift $ throwError e
    catchError (ECTrans a) h = ECTrans $ catchError a $ runECTrans . h

zipFilter :: [Bool] -> [a] -> [a]
zipFilter bs = map snd . filter fst . zip bs

globalArgsMap :: Map.Map Ident [Bool]
globalArgsMap = Map.fromList
  [ ("Prelude.take", [False, True, False, True])
  , ("Prelude.drop", [False, False, True, True])
  ]

translateIdent :: Ident -> EC.Ident
translateIdent i =
  case i of
    "Prelude.False" -> "false"
    "Prelude.True" -> "true"
    "Prelude.take" -> "take"
    "Prelude.drop" -> "drop"
    _ -> show i

translateApp :: (Termlike t) =>
                Map.Map Ident [Bool] ->
                t ->
                [t] ->
                ECTrans EC.Expr
translateApp argsMap (asGlobalDef -> Just i) args =
  EC.App (EC.ModVar (translateIdent i)) <$> traverse translateTerm args'
    where
      args' = (maybe id zipFilter (Map.lookup i argsMap)) args
translateApp _ _ _ = throwError $ NotSupported

flatTermFToExpr ::
  (t -> ECTrans EC.Expr) ->
  FlatTermF t ->
  ECTrans EC.Expr
flatTermFToExpr transFn tf =
  case tf of
    GlobalDef i   -> EC.ModVar <$> pure (translateIdent i)
    UnitValue     -> EC.Tuple <$> pure []
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
    CtorApp _ _      -> notExpr
    DataTypeApp _ _ -> notExpr
    Sort _ -> notExpr
    NatLit i -> EC.IntLit <$> pure i
    ArrayValue _ _ -> notSupported
    FloatLit _  -> notSupported
    DoubleLit _ -> notSupported
    StringLit _ -> notSupported
    ExtCns (EC _ _ _) -> notSupported
  where
    notExpr = throwError $ NotExpr
    notSupported = throwError $ NotSupported

flatTermFToType ::
  (t -> ECTrans EC.Type) ->
  FlatTermF t ->
  ECTrans EC.Type
flatTermFToType _transFn tf =
  case tf of
    GlobalDef _   -> notType
    UnitValue     -> notType
    UnitType      -> notSupported
    PairValue _ _ -> notType
    PairType _ _  -> notSupported
    PairLeft _    -> notType
    PairRight _   -> notType
    EmptyValue         -> notType
    EmptyType          -> pure $ EC.TupleTy []
    FieldValue _ _ _   -> notType
    FieldType _ _ _    -> notSupported
    RecordSelector _ _ -> notType
    CtorApp _ _      -> notSupported
    DataTypeApp _ _  -> notSupported
    Sort _ -> notType
    NatLit _ -> notType
    ArrayValue _ _ -> notType
    FloatLit _  -> notType
    DoubleLit _ -> notType
    StringLit _ -> notType
    ExtCns (EC _ _ _) -> notType
  where
    notType = throwError $ NotType
    notSupported = throwError $ NotSupported

translateTerm :: (Termlike t) => t -> ECTrans EC.Expr
translateTerm t =
  case t of
    (asFTermF -> Just tf)  -> flatTermFToExpr translateTerm tf
    (asLambda -> Just _) -> EC.Binding EC.Lambda <$> undefined <*> translateTerm e
      where (_args, e) = asLambdaList t
    (asApp -> Just _) -> translateApp globalArgsMap f as
      where (f, as) = asApplyAll t
    (asLocalVar -> Just i) -> EC.LocalVar <$> pure (show i)
    _ -> notSupported
  where
    notSupported = throwError $ NotSupported

translateTermDoc :: Term -> Either (TranslationError Term) Doc
translateTermDoc t = do
  (expr, defs) <- runWriterT $ runECTrans $ translateTerm t
  return $ (vcat (map ppDef defs)) <$$> ppExpr expr
