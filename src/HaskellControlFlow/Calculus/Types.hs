{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Types where

import HaskellControlFlow.Calculus.Calculus

import Control.Applicative
import Control.Worklist
import qualified Data.Map as M
import Data.List
import Data.Maybe

-- | Represents a program within our supported subset of Haskell. Consists of a top-level 
--   expression (all functions are nested let expressions) and a collection of defined data types.
data HaskellProgram a = HaskellProgram {dataTypes :: DataEnv, topExpr :: Term a}

-- | A Haskell type. May also contain function type annotations or type variables.
--   Since lists and tuples are parametrized and can therefore not be generally defined in the 
--   subset of Haskell we support, they are considered as special cases.
data Type = BasicType BasicType
          | DataType (Maybe AnnVar) Name
          | ListType (Maybe AnnVar) Type
          | TupleType (Maybe AnnVar) [Type]
          | Arrow (Maybe AnnVar) Bool Type Type
          | TyVar Name
          -- | Forall Name Type (polymorphism)
          deriving Eq

instance Show Type where
    showsPrec n (BasicType k) = showsPrec n k
    showsPrec _ (DataType x k) = (k++)
    showsPrec _ (ListType _ ty)
        = ("["++)
        . showsPrec 0 ty
        . ("]"++)
    showsPrec _ (TupleType _ tys)
        = ("("++)
        . (intercalate ", " (map (\t -> showsPrec 0 t "") tys) ++)
        . (")"++)
    showsPrec n (Arrow _ _ lhs rhs)
        = ((if n > 0 then "(" else "")++)
        . showsPrec 10 lhs
        . (" -> "++)
        . showsPrec 0 rhs
        . ((if n > 0 then ")" else "")++)
    showsPrec _ (TyVar k) = (k++)

-- | A few build-in types.
data BasicType = Integer
               | Char
               | Double
                 deriving (Eq, Show)

-- | Annotation variable.
type AnnVar = Name

-- | A type environment: a mapping from variable names to their inferred types.
type TyEnv = M.Map Name Type

-- | Returns a possible type annotation.
typeAnn :: Type -> Maybe AnnVar
typeAnn (Arrow ann _ _ _) = ann
typeAnn _                 = Nothing

-- | Gives the type with a certain name. Either returns a basic type if the String equals "Integer",
--   "Char" or "Double"; or considers the type to be a custom data type.
typeFromName :: String -> Type
typeFromName "Int"     = BasicType Integer
typeFromName "Integer" = BasicType Integer
typeFromName "Char"    = BasicType Char
typeFromName "Double"  = BasicType Double
typeFromName datatype  = DataType Nothing datatype

-- | An environment of types of some standard functions with which basic types can be manipulated.
initTyEnv :: TyEnv
initTyEnv = M.fromList stdOps
 where stdOps = [
                   ("negate"       , BasicType Integer .> BasicType Integer)
                 , ("+"            , BasicType Integer .> BasicType Integer .> BasicType Integer)
                 , ("-"            , BasicType Integer .> BasicType Integer .> BasicType Integer)
                 , ("*"            , BasicType Integer .> BasicType Integer .> BasicType Integer)
                 , ("div"          , BasicType Integer .> BasicType Integer .> BasicType Integer)
                 , ("ord"          , BasicType Char    .> BasicType Integer)
                 , ("chr"          , BasicType Integer .> BasicType Char   )
                 , ("round"        , BasicType Double  .> BasicType Integer)
                 , ("fromIntegral" , BasicType Integer .> BasicType Double )
                 , ("/"            , BasicType Double  .> BasicType Double  .> BasicType Double )
                ]
       a .> b = Arrow Nothing False a b
       infixr 3 .>

-- | Definition of a custom Haskell98 algebraic data type. May be (non-mutually) recursive, but 
--   must be regular and can not be paramterized.
data DataDef = DataDef {dataName :: Name, ctors :: [DataCon]}

-- | Definition of one constructor within a data type.
data DataCon = DataCon {conName :: Name, members :: [Type]}

-- | Bool data definition. This is a regular data type, but needs to be present in order to support
--   if expressions and guards and such.
boolDef :: DataDef
boolDef = DataDef "Bool" [DataCon "True" [], DataCon "False" []]

-- | Environment of user-defined data types. Also contains a mapping from constructor names to
--   data definition names.
data DataEnv = DataEnv {ddefs :: M.Map Name DataDef, conNameMap :: M.Map Name Name}

-- | Initial environment containing solely the bool type.
initEnv :: DataEnv
initEnv = addDataDef boolDef $ DataEnv M.empty M.empty

-- | Look up the definition of a data type with a certain name.
lookupDataDef :: Name -> DataEnv -> Maybe DataDef
lookupDataDef n = M.lookup n . ddefs

-- | Look up the data type which contains a constructor with a particular name, as well as the 
--   types of the constructor arguments.
lookUpConTypes :: Name -> DataEnv -> Maybe (Type, [Type])
lookUpConTypes n env = do dname <- M.lookup n $ conNameMap env
                          def   <- M.lookup dname $ ddefs env
                          con   <- find (\c -> conName c == n) $ ctors def
                          return (DataType Nothing dname, members con)

-- | Add a data definition to the environment.
addDataDef :: DataDef -> DataEnv -> DataEnv
addDataDef def env = env {ddefs = M.insert dname def (ddefs env), conNameMap = addCons $ ctors def}
 where dname = dataName def
       addCons cs = foldr (\(DataCon n _) -> (M.insert n dname .)) id cs $ conNameMap env
