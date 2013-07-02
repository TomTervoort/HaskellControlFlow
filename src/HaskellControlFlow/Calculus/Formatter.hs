{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Formatter (formatCalculus) where

import HaskellControlFlow.Calculus.Calculus

import Data.List

-- Formats a calculus.
formatCalculus :: Calculus -> String
formatCalculus term = (formatTerm term "") ++ "\n"

-- Formats a term.
formatTerm :: Term -> String -> String
formatTerm term indentation = case term of
    ConstantTerm {constant = constant} ->
        formatConstant constant
    VariableTerm {varName = varName} ->
        varName
    ApplicationTerm {lhsTerm = lhsTerm, rhsTerm = rhsTerm} ->
        '(' : formatTerm lhsTerm indentation ++ ' ' : (formatTerm rhsTerm indentation) ++ ")"
    AbstractionTerm {argName = argName, bodyTerm = bodyTerm} ->
        '\\' : argName ++ " -> " ++ formatTerm bodyTerm indentation
    LetInTerm {letTerm = letTerm, inTerm = inTerm} ->
        "\n" ++ indentation ++ "let" ++ formatNamedTerm letTerm ('\t' : indentation) ++
        "\n" ++ indentation ++ "in\n\t" ++ indentation ++ formatTerm inTerm ('\t' : indentation)
    CaseTerm {exprTerm = exprTerm, alts = alts} ->
        "\n" ++ indentation ++ "case " ++ formatTerm exprTerm indentation ++ " of"
        ++ concatMap (\(patt, expr) -> formatPattern patt ++ " -> " ++ formatTerm expr ('\t' : indentation)) alts
    ListTerm terms -> concat $ ["["] ++ intersperse ", " (map fmt terms) ++ ["]"]
    TupleTerm terms -> concat $ ["("] ++ intersperse ", " (map fmt terms) ++ [")"]
 where fmt t = formatTerm t indentation

-- Formats a named term.
formatNamedTerm :: NamedTerm -> String -> String
formatNamedTerm NamedTerm {name = name, term = term} indentation =
    "\n" ++ indentation ++ name ++ " = " ++ formatTerm term ('\t' : indentation)

-- Formats a constant.
formatConstant :: Constant -> String
formatConstant constant = case constant of
    IntegerConst integer -> show integer
    DoubleConst rational -> show rational
    StringConst string   -> show string
    CharConst char       -> show char

formatPattern :: Pattern -> String
formatPattern (Variable name) = name
formatPattern (Pattern ctor args) = "(" ++ ctor ++ concatMap (" "++) args ++ ")"
