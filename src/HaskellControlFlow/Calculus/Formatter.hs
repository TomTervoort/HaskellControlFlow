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
    ConstantTerm {constant = constant} ->
        formatConstant constant
    VariableTerm {varName = varName} ->
        varName
    ApplicationTerm {lhsTerm = lhsTerm, rhsTerm = rhsTerm} ->
        '(' : formatTermHelper lhsTerm indentation ++ ' ' : (formatTermHelper rhsTerm indentation) ++ ")"
    AbstractionTerm {argName = argName, bodyTerm = bodyTerm} ->
        '\\' : argName ++ " -> " ++ formatTermHelper bodyTerm indentation
    LetInTerm {letTerm = letTerm, inTerm = inTerm} ->
        "\n" ++ indentation ++ "let" ++ formatNamedTerm letTerm ('\t' : indentation) ++
        "\n" ++ indentation ++ "in\n\t" ++ indentation ++ formatTermHelper inTerm ('\t' : indentation)
    CaseTerm {exprTerm = exprTerm, alts = alts} ->
        "\n" ++ indentation ++ "case " ++ formatTermHelper exprTerm indentation ++ " of"
        ++ concatMap (\(patt, expr) -> "\n\t" ++ indentation ++ formatPattern patt ++ " -> " ++ formatTermHelper expr ('\t' : indentation)) alts
    ListTerm {terms = terms} -> 
        "[" ++ intercalate ", " (map (flip formatTermHelper "") terms) ++ "]"
    TupleTerm {terms = terms} -> 
        "(" ++ intercalate ", " (map (flip formatTermHelper "") terms) ++ ")"
    FixTerm {fixedTerm = term} ->
        "fix (" ++ formatTermHelper term "" ++ ")"

-- Formats a named term.
formatNamedTerm :: NamedTerm a -> String -> String
formatNamedTerm NamedTerm {name = name, term = term} indentation =
    "\n" ++ indentation ++ name ++ " = " ++ formatTermHelper term ('\t' : indentation)

-- Formats a constant.
formatConstant :: Constant -> String
formatConstant constant = case constant of
    IntegerConst integer -> show integer
    DoubleConst rational -> show rational
    StringConst string   -> show string
    CharConst char       -> show char

formatPattern :: Pattern -> String
formatPattern (Variable name) = name
formatPattern (Pattern ctor args) = "(" ++ ctor ++ concatMap (' ':) args ++ ")"
