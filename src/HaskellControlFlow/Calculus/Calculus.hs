{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Calculus where

-- | Extended lambda calculus.
type Calculus = Term

-- | Terms.
data Term = ConstantTerm {constant :: Constant}
          | VariableTerm {varName :: Name}
          | ApplicationTerm {lhsTerm :: Term, rhsTerm :: Term}
          | AbstractionTerm {argName :: Name, bodyTerm :: Term}
          | LetInTerm {letTerm :: NamedTerm, inTerm :: Term}
          | CaseTerm {exprTerm :: Term, alts :: [(Pattern, Term)]}          
          | ListTerm {terms :: [Term]}
          | TupleTerm {terms :: [Term]}
            deriving (Show)

-- | Smart constructor for multiple let-terms following each other in an expression.
multipleLets :: [NamedTerm] -> Term -> Term
multipleLets [NamedTerm n def] t = LetInTerm (NamedTerm n def) t
multipleLets (n:ns) t = LetInTerm n $ multipleLets ns t
multipleLets [] _ = error "Provide at least one named term."

-- | Patterns within case-expressions.
data Pattern = Variable Name
             | Pattern {ctorName :: Name, ctorArgs :: [Name]}
               deriving (Show)

-- | Named term.
data NamedTerm = NamedTerm {name :: Name, term :: Term}
                 deriving (Show)

-- | Constants.
data Constant = IntegerConst Integer
              | DoubleConst Rational
              | StringConst String
              | CharConst Char
                deriving (Show)

-- | Abstraction name.
type Name = String
