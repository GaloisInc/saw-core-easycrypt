{-# LANGUAGE
  FlexibleInstances,
  GeneralizedNewtypeDeriving,
  MultiParamTypeClasses
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
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.EasyCrypt.AST as EC
import Data.EasyCrypt.Pretty
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor

data TranslationError t
  = NotSupported
  | NotExpr
  | NotType

newtype ECTrans a = ECTrans {
      runECTrans :: WriterT [EC.Binding] (Either (TranslationError Term)) a
    }
  deriving (Applicative, Functor, Monad)

instance MonadError (TranslationError Term) ECTrans where
    throwError e = ECTrans $ lift $ throwError e
    catchError (ECTrans a) h = ECTrans $ catchError a $ runECTrans . h

flatTermFToExpr ::
  (t -> ECTrans EC.Expr) ->
  FlatTermF t ->
  ECTrans EC.Expr
flatTermFToExpr transFn tf =
  case tf of
    GlobalDef i   -> EC.ModVar <$> pure (show i)
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

{-
flatTermFToType ::
  (MonadWriter EC.Binding m) =>
  (t -> m EC.Type) ->
  FlatTermF t ->
  m EC.Tupe
flatTermFToType transFn tf =
    GlobalDef _   -> notType
    UnitValue     -> notType
    UnitType      -> notSupported
    PairValue _ _ -> notType
    PairType x y  ->
    PairLeft _    -> notType
    PairRight _   -> notType
    EmptyValue         -> notType
    EmptyType          -> pure $ RecordTDoc []
    FieldValue _ _ _   -> notType
    FieldType f x y    -> ppFieldType <$> pp PrecNone f <*> pp PrecNone x <*> pp PrecNone y
    RecordSelector _ _ -> notType
    CtorApp c l      -> TermDoc . ppAppList prec (ppIdent c) <$> traverse transFn l
    DataTypeApp dt l -> TermDoc . ppAppList prec (ppIdent dt) <$> traverse transFn l
    Sort s -> pure $ TermDoc $ text (show s)
    NatLit _ -> notType
    ArrayValue _ _ -> notType
    FloatLit _  -> notType
    DoubleLit _ -> notType
    StringLit _ -> notType
    ExtCns (EC _ _ _) -> notType
-}

termFToExpr ::
  (t -> ECTrans EC.Expr) ->
  TermF t ->
  ECTrans EC.Expr
termFToExpr transFn t =
  case t of
    FTermF tf -> flatTermFToExpr transFn tf
    -- TODO: traverse all bindings for saturated binding
    Lambda _ _ e -> EC.Binding EC.Lambda <$> undefined <*> transFn e
    Pi _ _ _ -> notSupported
    -- TODO: traverse all arguments for saturated application
    App f e -> EC.App <$> transFn f <*> traverse transFn [e]
    Let _ _ -> notSupported
    LocalVar i -> EC.LocalVar <$> pure (show i)
    Constant _ _ _ -> notSupported
  where
    notSupported = throwError $ NotSupported

translateTerm :: (Termlike t) => t -> ECTrans EC.Expr
translateTerm t = termFToExpr translateTerm (unwrapTermF t)

translateTermDoc :: Term -> ECTrans Doc
translateTermDoc t = ppExpr <$> translateTerm t
