{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Formatter (formatTerm) where

import Data.List (intercalate)
import HaskellControlFlow.Calculus.Calculus

import Data.List

-- | Formats a term.
formatTerm :: Term a -> String
formatTerm term = (formatTermHelper term "") ++ "\n"

-- | Formats a term helper.
formatTermHelper :: Term a -> String -> String
formatTermHelper term indentation = case term of
    LiteralTerm _ c ->
        formatConstant c
    VariableTerm _ n ->
        n
    HardwiredTerm _ h ->
        show h
    ApplicationTerm _ lhsTerm rhsTerm ->
        '(' : formatTermHelper lhsTerm indentation ++ ' ' : (formatTermHelper rhsTerm indentation) ++ ")"
    AbstractionTerm _ argName bodyTerm ->
        '\\' : argName ++ " -> " ++ formatTermHelper bodyTerm indentation
    LetInTerm _ binder letTerm inTerm ->
        "\n" ++ indentation ++ "let" ++ formatNamedTerm binder letTerm ('\t' : indentation) ++
        "\n" ++ indentation ++ "in\n\t" ++ indentation ++ formatTermHelper inTerm ('\t' : indentation)
    CaseTerm _ scrutinee alternatives ->
        "\n" ++ indentation ++ "case " ++ formatTermHelper scrutinee indentation ++ " of"
        ++ concatMap (\(patt, expr) -> "\n\t" ++ indentation ++ formatPattern patt ++ " -> " ++ formatTermHelper expr ('\t' : indentation)) alternatives
    FixTerm _ term ->
        "fix (" ++ formatTermHelper term "" ++ ")"

-- Formats a named term.
formatNamedTerm :: Name -> Term a -> String -> String
formatNamedTerm name term indentation =
    "\n" ++ indentation ++ name ++ " = " ++ formatTermHelper term ('\t' : indentation)

-- Formats a constant.
formatConstant :: Literal -> String
formatConstant constant = case constant of
    IntegerLit integer -> show integer
    RationalLit rational -> show rational
    StringLit string   -> show string
    CharLit char       -> show char

formatPattern :: Pattern -> String
formatPattern (Variable name) = name
formatPattern (Pattern ctor args) = "(" ++ ctor ++ concatMap (' ':) args ++ ")"
