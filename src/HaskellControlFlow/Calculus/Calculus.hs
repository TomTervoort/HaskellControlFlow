{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Calculus where

-- Extended lambda calculus.
data Calculus = Term

-- Terms.
data Term = ConstantTerm {constant :: Constant}
          | ApplicationTerm {lhsTerm :: Term, rhsTerm :: Term}
          | AbstractionTerm {argName :: Name, bodyTerm :: Term}
          | LetInTerm {letName :: Name, letTerm :: Term, inTerm :: Term}
          | IfTerm {exprTerm :: Term, thenTerm :: Term, elseTerm :: Term}
          
          -- TODO: Operators. Named abstractions. Variables.
          
            deriving (Show)

-- Constants.
data Constant = IntegerConst Integer
              | DoubleConst Rational
              | StringConst String
              | CharConst Char
                 deriving (Show)

-- Abstraction name.
type Name = String

