{- |
Module      : Verifier.SAW.Export.EasyCrypt
Copyright   : Galois, Inc. 2017
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable (TODO?)
-}

module Verifier.SAW.Export.EasyCrypt where

import Text.PrettyPrint.ANSI.Leijen

import qualified Data.EasyCrypt.AST as EC
import Data.EasyCrypt.Pretty
import Verifier.SAW.SharedTerm

translateTerm :: Term -> EC.Expr
translateTerm = undefined

translateTermDoc :: Term -> Doc
translateTermDoc = ppExpr . translateTerm
