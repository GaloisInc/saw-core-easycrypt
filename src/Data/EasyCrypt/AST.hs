{- |
Module      : Data.EasyCrypt.AST
Copyright   : Galois, Inc. 2017
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Data.EasyCrypt.AST where

type Ident = String

data Quantifier
  = Lambda
  -- | Forall
  -- | Exists

data Type
  = TyVar Ident
  | TupleTy [Type]
  | TyConstr Ident [Type]
  | FunTy Type Type

type Binding = (Ident, Maybe Type)

data LPattern
  = LSymbol Ident Type
  | LTuple [(Ident, Type)]
  -- | LRecord

data Expr
  = IntLit Int
  | LocalVar Ident
  | ModVar Ident
  | App Expr [Expr]
  | Binding Quantifier [Binding] Expr
  | Let LPattern Expr Expr
  | Tuple [Expr]
  | If Expr Expr Expr
  -- | Match Expr [Expr] Type
  | Project Expr Int
