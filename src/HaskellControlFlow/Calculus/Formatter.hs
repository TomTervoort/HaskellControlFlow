{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Formatter (formatCalculus) where

import HaskellControlFlow.Calculus.Calculus

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
    LetInTerm {letTerms = letTerms, inTerm = inTerm} ->
        "\n" ++ indentation ++ "let" ++ (concatMap (\term -> formatNamedTerm term ('\t' : indentation)) letTerms) ++
        "\n" ++ indentation ++ "in\n\t" ++ indentation ++ formatTerm inTerm ('\t' : indentation)
    IfTerm {exprTerm = exprTerm, thenTerm = thenTerm, elseTerm = elseTerm} -> 
        "\n" ++ indentation ++ "if\n\t" ++ indentation ++ formatTerm exprTerm ('\t' : indentation) ++
        "\n" ++ indentation ++ "then" ++
        "\n\t" ++ indentation ++ formatTerm thenTerm ('\t' : indentation) ++
        "\n" ++ indentation ++ "else" ++
        "\n\t" ++ indentation ++ formatTerm elseTerm ('\t' : indentation)

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
    
