{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.TypedCalculus where

import qualified HaskellControlFlow.Calculus.Calculus as C
import HaskellControlFlow.Calculus.Types

-- | Extended lambda calculus.
type TypedCalculus = TypedTerm

-- | Typed terms.
data TypedTerm = TypedConstantTerm {termType :: Type, constant :: C.Constant}
               | TypedVariableTerm {termType :: Type, varName :: C.Name}
               | TypedApplicationTerm {termType :: Type, lhsTerm :: TypedTerm, rhsTerm :: TypedTerm}
               | TypedAbstractionTerm {termType :: Type, argName :: C.Name, bodyTerm :: TypedTerm}
               | TypedLetInTerm {termType :: Type, letTerm :: NamedTypedTerm, inTerm :: TypedTerm}
               | TypedCaseTerm {termType :: Type, exprTerm :: TypedTerm, alts :: [(C.Pattern, TypedTerm)]}          
               | TypedListTerm {termType :: Type, terms :: [TypedTerm]}
               | TypedTupleTerm {termType :: Type, terms :: [TypedTerm]}
                 deriving (Show)

-- | Named typed term.
data NamedTypedTerm = NamedTypedTerm {name :: C.Name, term :: TypedTerm}
                      deriving (Show)

-- | Helper method for constants.
typedConstantTerm :: Type -> C.Term -> TypedTerm
typedConstantTerm termType term =
    TypedConstantTerm {termType = termType, constant = C.constant term}

-- | Helper method for variables.
typedVariableTerm :: Type -> C.Term -> TypedTerm
typedVariableTerm termType term =
    TypedVariableTerm {termType = termType, varName = C.varName term}

-- | Helper method for applications.
typedApplicationTerm :: Type -> C.Term -> TypedTerm -> TypedTerm -> TypedTerm
typedApplicationTerm termType _ lhsTerm rhsTerm =
    TypedApplicationTerm {termType = termType, lhsTerm = lhsTerm, rhsTerm = rhsTerm}

-- | Helper method for abstractions.
typedAbstractionTerm :: Type -> C.Term -> TypedTerm -> TypedTerm
typedAbstractionTerm termType term bodyTerm =
    TypedAbstractionTerm {termType = termType, argName = C.argName term, bodyTerm = bodyTerm}

-- | Helper method for let in terms.
typedLetInTerm :: Type -> C.Term -> NamedTypedTerm -> TypedTerm -> TypedTerm
typedLetInTerm termType _ letTerm inTerm =
    TypedLetInTerm {termType = termType, letTerm = letTerm, inTerm = inTerm}

-- | Helper method for case terms.
typedCaseTerm :: Type -> C.Term -> TypedTerm -> [(C.Pattern, TypedTerm)] -> TypedTerm
typedCaseTerm termType _ exprTerm alts =
    TypedCaseTerm {termType = termType, exprTerm = exprTerm, alts = alts}

-- | Helper method for list terms.
typedListTerm :: Type -> C.Term -> [TypedTerm] -> TypedTerm
typedListTerm termType _ terms =
    TypedListTerm {termType = termType, terms = terms}

-- | Helper method for tuple terms.
typedTupleTerm :: Type -> C.Term -> [TypedTerm] -> TypedTerm
typedTupleTerm termType _ terms =
    TypedTupleTerm {termType = termType, terms = terms}

-- | Helper method for named typed terms.
namedTypedTerm :: C.Name -> TypedTerm -> NamedTypedTerm
namedTypedTerm = NamedTypedTerm
