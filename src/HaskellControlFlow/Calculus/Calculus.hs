{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Calculus where

-- Extended lambda calculus.
type Calculus = Term

-- Terms.
data Term = ConstantTerm {constant :: Constant}
          | VariableTerm {varName :: Name}
          | ApplicationTerm {lhsTerm :: Term, rhsTerm :: Term}
          | AbstractionTerm {argName :: Name, bodyTerm :: Term}
          | LetInTerm {letTerms :: [NamedTerm], inTerm :: Term}
          | IfTerm {exprTerm :: Term, thenTerm :: Term, elseTerm :: Term}
          
          -- TODO: Operators.
          
            deriving (Show)

-- Named term.
data NamedTerm = NamedTerm {name :: Name, term :: Term}
                 deriving (Show)

-- Constants.
data Constant = IntegerConst Integer
              | DoubleConst Rational
              | StringConst String
              | CharConst Char
                deriving (Show)

-- Abstraction name.
type Name = String

