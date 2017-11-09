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
  deriving (Show)

data Type
  = TyVar Ident
  | TupleTy [Type]
  | FunTy Type Type
  | TyApp Ident [Type]
  deriving (Show)

type Binding = (Ident, Maybe Type)

data LPattern
  = LSymbol Ident Type
  | LTuple [(Ident, Type)]
  -- | LRecord
  deriving (Show)

data Expr
  = IntLit Integer
  | LocalVar Ident
  | ModVar Ident
  | App Expr [Expr]
  | Binding Quantifier [Binding] Expr
  | Let LPattern Expr Expr
  | Tuple [Expr]
  | If Expr Expr Expr
  -- | Match Expr [Expr] Type
  | TupleProject Expr Int
  | Record [RecordField]
  | RecordProject Expr Ident
  deriving (Show)

data RecordField = RecordField Ident Expr
  deriving (Show)

data Decl
  = OpDecl Ident [Binding] Expr
  | TypeDecl Ident [Ident] Type -- for now we exclude abstract types
                                -- and subtyping constraints
  deriving (Show)
