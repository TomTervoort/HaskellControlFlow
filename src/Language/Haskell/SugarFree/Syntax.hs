{-# LANGUAGE Haskell2010 #-}
{- |

Module      : Language.Haskell.SugarFree.Syntax
Description : Sugar-free syntax of Haskell 2010
Copyright   : (c) Stijn van Drongelen
License     : CC0

Maintainer  : rhymoid@gmail.com
Stability   : experimental
Portability : portable

A syntax for Haskell 2010, but without all the sugar. Sadly, this module still
misses some critical components:

* guards
* statements
* modules, imports, exports, FFI
* type classes
* instance derivation
* records

Further TODOs:

* Figure out a way to have a type-level guarantee that all identifiers are
  fresh.

-}
module Language.Haskell.SugarFree.Syntax where

import Data.List
import qualified Data.Text as T

---

data Qualification
    = Unqualified
    | Qualified [T.Text]

data SyntaxFlavour
    = Wordy
    | Symbolic

data Identifier p
    = Identifier !Qualification !SyntaxFlavour !T.Text

instance Show (Identifier p) where
    show (Identifier Unqualified _ x) = T.unpack x
    show (Identifier (Qualified ms) _ x) = intercalate "." (map T.unpack (ms ++ [x]))

data BindName p
    = Blank
    | BindName !(Identifier p)
    | BindFresh !Integer

instance Show (BindName p) where
    show Blank = "_"
    show (BindName x) = show x
    show (BindFresh i) = "fresh#" ++ show i

data UseName p
    = UseName !(Identifier p)
    | UseFresh !Integer
    | UseHardwired (HardwiredIdentifier p)

-- TODO Turn into a GADT?
data HardwiredIdentifier p
    = HwTupleType !Int
    | HwTupleValue !Int
    | HwListNil
    | HwListCons
    | HwListType
    | HwFunctionType
    | HwNegate
    | HwEnumFrom
    | HwEnumFromTo
    | HwEnumFromThen
    | HwEnumFromThenTo
    | HwBool
    | HwTrue
    | HwFalse
    | HwConcatMap
    | HwMonadFail
    | HwMonadSequence
    | HwMonadBind
    | HwEqualsValue
    -- HwEqualsType
    | HwNumClass
    | HwEqClass
    | HwOrdClass

instance Show (UseName p) where
    show (UseName x) = show x
    show (UseFresh i) = "fresh#" ++ show i
    show (UseHardwired hw) = show hw

instance Show (HardwiredIdentifier p) where
    show (HwTupleType k) = "(" ++ replicate k ',' ++ ")"
    show (HwTupleValue k) = "(" ++ replicate k ',' ++ ")"
    show HwListNil = "([])"
    show HwListCons = "(:)"
    show HwListType = "([])"
    show HwFunctionType = "(->)"
    show HwNegate = "negate"
    show HwEnumFrom = "enumFrom"
    show HwEnumFromTo = "enumFromTo"
    show HwEnumFromThen = "enumFromThen"
    show HwEnumFromThenTo = "enumFromThenTo"
    show HwBool = "Bool"
    show HwTrue = "True"
    show HwFalse = "False"
    show HwConcatMap = "concatMap"
    show HwMonadFail = "fail"
    show HwMonadSequence = "(>>)"
    show HwMonadBind = "(>>=)"
    show HwEqualsValue = "(==)"
    -- show HwEqualsType = "(~)"
    show HwNumClass = "Num"
    show HwEqClass = "Eq"
    show HwOrdClass = "Ord"

---

data ValueLevel
data TypeLevel
data KindLevel

---

data Module
    = Module [Declaration]

data Declaration
    = ExprDecl (BindName ValueLevel) (ValueExpr)
    | DataDecl (BindName TypeLevel) (Maybe (KindExpr)) [ConstructorDecl]
    | SignatureDecl (BindName ValueLevel) (TypeExpr)
    -- TODO Type class, type instance
    -- TODO FFI

data ConstructorDecl
    = ConstructorDecl (BindName ValueLevel) (TypeExpr)

data ValueExpr
    = Use       (UseName ValueLevel)
    | Literal   Literal
    | Apply     (ValueExpr) (ValueExpr)
    | Abstract  (BindName ValueLevel) (ValueExpr)
    | Declare   (Declaration) (ValueExpr)
    | Match     (Matching)
    | Signature (TypeExpr) (ValueExpr)

data TypeExpr
    = UseT       (UseName TypeLevel)
    | ApplyT     (TypeExpr) (TypeExpr)
    | AbstractT  (BindName TypeLevel) (TypeExpr)
    | UniversalT (BindName TypeLevel) (TypeExpr)
    | ConstrainT (TypeConstraint) (TypeExpr)
    | SignatureT (KindExpr) (TypeExpr)

curryFunctionType :: ([TypeExpr], TypeExpr) -> TypeExpr
curryFunctionType (tys, tyt)
    = foldl (\lhs rhs -> ApplyT (ApplyT (UseT (UseHardwired HwFunctionType)) lhs) rhs) tyt tys

-- uncurryFunctionType :: TypeExpr -> ([TypeExpr], TypeExpr)

data TypeConstraint
    = InstanceConstraint (TypeExpr)
    | EqualityConstraint (TypeExpr) (TypeExpr) 

data KindExpr
    = KindStar
    | KindArrow (KindExpr) (KindExpr)

data Matching
    = Destruct (ValueExpr) [(Patt, Matching)]
    | Accept (ValueExpr)

data Patt
    = Whatever
    | Constructor (UseName ValueLevel) [Patt]
    | Alias (BindName ValueLevel) (Patt)

instance Show (Patt) where
    show Whatever = "_"
    show (Constructor c ps) = "(" ++ show c ++ intercalate " " (map show ps) ++ ")"
    show (Alias b Whatever) = show b
    show (Alias b p) = show b ++ "@" ++ show p

data Literal
    = LitChar   Char        !Bool
    | LitString T.Text      !Bool
    | LitInt    Integer     !Bool
    | LitFrac   Rational    !FracPrimness

data FracPrimness
    = NotFracPrim
    | FracPrimFloat
    | FracPrimDouble

instance Show Literal where
    show (LitChar   v p) = show v ++ if p then "#" else ""
    show (LitString v p) = show v ++ if p then "#" else ""
    show (LitInt    v p) = show v ++ if p then "#" else ""
    show (LitFrac   v p) = show v ++ case p of
        NotFracPrim -> ""
        FracPrimFloat -> "#"
        FracPrimDouble -> "##"
