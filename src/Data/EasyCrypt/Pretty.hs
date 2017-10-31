{- |
Module      : Data.EasyCrypt.Pretty
Copyright   : Galois, Inc. 2017
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Data.EasyCrypt.Pretty where

import Text.PrettyPrint.ANSI.Leijen
import Data.EasyCrypt.AST

-- TODO: import SAWCore pretty-printer?
tightSepList :: Doc -> [Doc] -> Doc
tightSepList _ [] = empty
tightSepList _ [d] = d
tightSepList s (d:l) = d <> s <+> commaSepList l

looseSepList :: Doc -> [Doc] -> Doc
looseSepList _ [] = empty
looseSepList _ [d] = d
looseSepList s (d:l) = d <+> s <+> commaSepList l

commaSepList, starSepList :: [Doc] -> Doc
commaSepList = tightSepList comma
starSepList = looseSepList (text "*")

period :: Doc
period = text "."

ppIdent :: Ident -> Doc
ppIdent = text

ppType :: Type -> Doc
ppType t =
  case t of
    TyVar x -> ppIdent x
    TupleTy tys -> parens (starSepList (map ppType tys))
    TyConstr x tys -> hsep (map ppType tys ++ [ppIdent x])
    FunTy fty aty -> ppType fty <+> text "->" <+> ppType aty

-- Anonymous bindings.
ppBinding :: Quantifier -> [Binding] -> Expr -> Doc
ppBinding q bs e =
  case q of
    Lambda ->
      parens (text "fun" <+> bindDocs <+> text "=>" <+> ppExpr e)
        where
          bindDocs = sep (map ppBind bs)

ppBind :: Binding -> Doc
ppBind (x, Nothing) = ppIdent x
ppBind (x, Just t) = parens (ppIdent x <+> colon <+> ppType t)

ppLet :: LPattern -> Expr -> Expr -> Doc
ppLet pat e e' =
  text "let" <+> bind <+> equals <+> ppExpr e <+> text "in" <+> ppExpr e'
    where
      bind = case pat of
               LSymbol x _ -> ppIdent x
               LTuple binds ->
                 parens (commaSepList (map (ppIdent . fst) binds))

ppExpr :: Expr -> Doc
ppExpr e =
  case e of
    IntLit n -> integer n
    LocalVar x -> ppIdent x
    ModVar x -> ppIdent x
    App f as -> sep (map ppExpr (f : as))
    Binding q bs body -> ppBinding q bs body
    Let pat e1 e2 -> ppLet pat e1 e2
    Tuple es -> parens (commaSepList (map ppExpr es))
    If c t f -> text "if" <+> ppExpr c <+>
                text "then" <+> ppExpr t <+>
                text "else" <+> ppExpr f
    TupleProject e1 n -> ppExpr e1 <> period <> int n
    Record fields -> encloseSep (text "{|") (text "|}") (text ";") (map ppRecordField fields)
    RecordProject record field -> ppExpr record <> text ".`" <> text field

ppDef :: Def -> Doc
ppDef (Def nm bs body) =
  hsep $ [text "op", text nm] ++ map ppBind bs ++ [equals, ppExpr body]

ppRecordField :: RecordField -> Doc
ppRecordField (RecordField name value) = ppIdent name <> text "=" <> ppExpr value
