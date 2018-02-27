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
import Control.Monad.State
import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.EasyCrypt.AST as EC
import Data.EasyCrypt.Pretty
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty
import Debug.Trace
import qualified Data.Vector as Vector (toList)

data TranslationError a
  = NotSupported a
  | NotExpr a
  | NotType a
  | LocalVarOutOfBounds a
  | BadTerm a

showError :: (a -> String) -> TranslationError a -> String
showError printer err = case err of
  NotSupported a -> "Not supported: " ++ printer a
  NotExpr a      -> "Expecting an expression term: " ++ printer a
  NotType a      -> "Expecting a type term: " ++ printer a
  LocalVarOutOfBounds a -> "Local variable reference is out of bounds: " ++ printer a
  BadTerm a -> "Malformed term: " ++ printer a

instance {-# OVERLAPPING #-} Show (TranslationError Term) where
  show = showError showTerm

  
instance {-# OVERLAPPABLE #-} Show a => Show (TranslationError a) where
  show = showError show 
  
newtype ECTrans a =
  ECTrans {
    runECTrans :: StateT
                  [EC.Decl]
                  (Either (TranslationError Term))
                  a
  }
  deriving (Applicative, Functor, Monad, MonadState [EC.Decl])

instance MonadError (TranslationError Term) ECTrans where
    throwError e = ECTrans $ lift $ throwError e
    catchError (ECTrans a) h = ECTrans $ catchError a $ runECTrans . h

zipFilter :: [Bool] -> [a] -> [a]
zipFilter bs = map snd . filter fst . zip bs

showFTermF :: FlatTermF Term -> String
showFTermF = show . Unshared . FTermF

-- arg order: outermost binding first
globalArgsMap :: Map.Map Ident [Bool]
globalArgsMap = Map.fromList
  [ ("Prelude.append", [False, False, False, True, True])
  , ("Prelude.take", [False, True, False, True])
  , ("Prelude.drop", [False, False, True, True])
  , ("Prelude.Vec", [False, True])
  , ("Prelude.uncurry", [False, False, False, True])
  , ("Prelude.map", [False, False, True, False, True])
  , ("Prelude.bvXor", [False, True, True])
  , ("Prelude.zipWith", [False, False, False, True, False, True, True])
  -- Assuming only finite Cryptol sequences
  , ("Cryptol.ecCat", [False, False, False, True, True])
  , ("Cryptol.seqZip", [False, False, False, False, True, True])
  , ("Cryptol.seqMap", [False, False, False, True, True])
  , ("Cryptol.ecSplit", [False, True, False, True])
  , ("Cryptol.ecXor", [False, True, True, True])
  , ("Cryptol.PLogicSeq", [False, False, True])
  , ("Cryptol.PLogicSeqBool", [False])
  , ("Cryptol.PLogicWord", [False])
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
    "Cryptol.ecCat" -> "(++)"
    "Prelude.take" -> "take"
    "Prelude.drop" -> "drop"
    "Prelude.zip" -> "zip"
    "Cryptol.seqZip" -> "zip"
    "Prelude.zipWith" -> "zipWith"
    "Prelude.uncurry" -> "sawcoreUncurry"
    "Prelude.map" -> "map"
    "Cryptol.seqMap" -> "map"
    "Prelude.bvXor" -> "sawcoreBVXor"
    "Cryptol.ecSplit" -> "cryptolECSplit"
    "Cryptol.Num" -> "int"
    "Cryptol.ecXor" -> "cryptolECXor"
    "Cryptol.PLogicSeq" -> "cryptolPLogicSeq"
    "Cryptol.PLogicSeqBool" -> "cryptolPLogicSeq"
    "Cryptol.PLogicWord" -> "cryptolPLogicWord"
    _ -> show i

traceFTermF :: String -> FlatTermF Term -> a -> a
traceFTermF ctx tf = traceTerm ctx (Unshared $ FTermF tf)
  
traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a

flatTermFToExpr ::
  (Term -> ECTrans EC.Expr) ->
  FlatTermF Term ->
  ECTrans EC.Expr
flatTermFToExpr transFn tf = traceFTermF "flatTermFToExpr" tf $
  case tf of
    GlobalDef i   -> EC.ModVar <$> pure (translateIdent i)
    UnitValue     -> EC.Tuple <$> pure [] -- TODO: hack
    UnitType      -> typePlaceholder -- notExpr
    PairValue x y -> EC.Tuple <$> traverse transFn [x, y]
    PairType _ _  -> typePlaceholder -- notExpr
    PairLeft t    -> EC.TupleProject <$> transFn t <*> pure 1
    PairRight t   -> EC.TupleProject <$> transFn t <*> pure 2
    EmptyValue    -> pure $ EC.Record []
    EmptyType     -> typePlaceholder -- notExpr
    FieldValue fname fvalue rest -> do
      fname' <- asString fname
      fvalue' <- transFn fvalue
      recr <- transFn rest
      case mergeRecordFields (EC.Record [EC.RecordField fname' fvalue']) recr of
        Just record -> return record
        Nothing     -> badTerm
    FieldType _ _ _    -> typePlaceholder -- notExpr
    RecordSelector record field -> do
      field' <- asString field
      (flip EC.RecordProject field') <$> transFn record
    CtorApp i []       -> EC.ModVar <$> pure (translateIdent i)
    CtorApp ctorName args ->
      EC.App <$> flatTermFToExpr transFn (CtorApp ctorName [])
             <*> mapM transFn args
    DataTypeApp _ _ -> typePlaceholder -- notExpr
    Sort _ -> notExpr
    NatLit i -> EC.IntLit <$> pure i
    ArrayValue _ vec -> EC.List <$> mapM transFn (Vector.toList vec)
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
    typePlaceholder = return (EC.Tuple [])

flatTermFToType ::
  (Term -> ECTrans EC.Type) ->
  FlatTermF Term ->
  ECTrans EC.Type
flatTermFToType transFn tf = traceFTermF "flatTermFToType" tf $
  case tf of
    GlobalDef i   -> EC.TyApp <$> pure (translateIdent i) <*> pure []
    UnitValue     -> notType
    UnitType      -> EC.TyApp <$> pure "unit" <*> pure []
    PairValue _ _ -> notType
    PairType x y  -> EC.TupleTy <$> traverse transFn [x, y]
    PairLeft _    -> notType
    PairRight _   -> notType
    EmptyValue         -> notType
    EmptyType          -> pure $ EC.TyVar Nothing
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
    Sort _ -> return (EC.TupleTy []) -- placeholder
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
translateType env t = traceTerm "translateType" t $
  case t of
    (asFTermF -> Just tf) -> flatTermFToType (translateType env) tf
    (asPi -> Just (_, ty, body)) ->
      EC.FunTy <$> translateType env ty <*> translateType env body
    (asSeq -> Just (_, tf)) -> mkECListType <$> translateType env tf
    -- (asVectorType -> Just (_, tf)) -> mkECListType <$> translateType env tf
    (asLocalVar -> Just n)
      | n < length env -> return (EC.TyVar (Just (env !! n)))
      | otherwise -> throwError $ LocalVarOutOfBounds t
    _ -> trace "translateType fallthrough" notSupported
  where
    notSupported = throwError $ NotSupported t
    mkECListType typ = EC.TyApp "list" [typ]

-- | Recognizes an $App (App "Cryptol.seq" n) x$ and returns ($n$, $x$).
asSeq :: Monad f => Recognizer f Term (Term, Term)
asSeq t = do (f, args) <- asApplyAllRecognizer t
             fid <- asGlobalDef f
             case (fid, args) of
               ("Cryptol.seq", [n, x]) -> return (n,x)
               _ -> fail "not a seq"
                            
asApplyAllRecognizer :: Monad f => Recognizer f Term (Term, [Term])
asApplyAllRecognizer t = do _ <- asApp t
                            return $ asApplyAll t

-- env is innermost first order
translateTerm :: [String] -> Term -> ECTrans EC.Expr
translateTerm env t = traceTerm "translateTerm" t $
  case t of
    (asFTermF -> Just tf)  -> flatTermFToExpr (translateTerm env) tf
    (asLambda -> Just _) -> do
      tys <- mapM (translateType env . snd) params
      EC.Binding EC.Lambda <$> pure (zip paramNames (map Just tys))
                           -- env is in innermost first (reverse) binder order
                           <*> translateTerm ((reverse paramNames) ++ env) e
        where
          -- params are in normal, outermost first, order
          (params, e) = asLambdaList t
          -- param names are in normal, outermost first, order
          paramNames = map fst $ params
    (asApp -> Just _) ->
      -- asApplyAll: innermost argument first
      let (f, args) = asApplyAll t
      in case f of
           (asGlobalDef -> Just i) ->
             case i of
                "Cryptol.unsafeCoerce" ->
                -- assuming unsafeCoerce is safe in SAW-Core generated
                -- by the Cryptol compiler, so we just strip it
                -- away. For now throwing away the type, but we'll see
                -- if we need to resulting type (second parameter) in
                -- practice.
                  translateTerm env (last args)
                "Prelude.unsafeCoerce" ->
                  translateTerm env (last args)
                "Prelude.fix" -> case args of
                  [resultType, lambda] -> 
                    case resultType of
                      -- TODO: check that 'n' is finite
                      (asSeq -> Just (n, _)) ->
                        case lambda of
                          (asLambda -> Just (x, ty, body)) | ty == resultType -> do
                              len <- translateTerm env n
                              -- let len = EC.App (EC.ModVar "size") [EC.ModVar x]
                              expr <- translateTerm (x:env) body
                              typ <- translateType env ty
                              return $ EC.App (EC.ModVar "iter") [len, EC.Binding EC.Lambda [(x, Just typ)] expr, EC.List []]
                          _ -> badTerm   
                      _ -> notSupported
                  _ -> badTerm
                _ -> EC.App <$> translateTerm env f
                            <*> traverse (translateTerm env) (filterArgs i args)
                  
           _ -> EC.App <$> translateTerm env f
                       <*> traverse (translateTerm env) args
    (asLocalVar -> Just n)
      | n < length env -> EC.LocalVar <$> pure (env !! n)
      | otherwise -> throwError $ LocalVarOutOfBounds t
    (unwrapTermF -> Constant n body _) -> do
      decls <- get
      if any (matchDecl n) decls
        then return ()
        else do
          b <- translateTerm env body
          case b of
            EC.Binding EC.Lambda args b' -> modify (EC.OpDecl n args b' :)
            _ -> modify (EC.OpDecl n [] b :)
      EC.ModVar <$> pure n
    _ -> trace "translateTerm fallthrough" notSupported
  where
    notSupported = throwError $ NotSupported t
    badTerm = throwError $ BadTerm t
    matchDecl n (EC.OpDecl n' _ _) = n == n'
    matchDecl _ _ = False

translateTermDoc :: Term -> Either (TranslationError Term) Doc
translateTermDoc t = do
  (expr, decls) <- runStateT (runECTrans $ translateTerm [] t) []
  return $ (vcat (map ppDecl (reverse decls))) <$$> ppExpr expr
