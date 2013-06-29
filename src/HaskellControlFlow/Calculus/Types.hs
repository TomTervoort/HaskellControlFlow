{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Types where

import HaskellControlFlow.Calculus.Calculus

import Data.Map (Map)
import qualified Data.Map as M

-- | A Haskell type. May also represent a type variable or contain function type annotations.
--   Since lists and tuples are parametrized and can therefore not be generally defined in the 
--   subset of Haskell we support, they are considered as special cases.
data Type = BasicType BasicType
          | DataType Name
          | ListType Type
          | TupleType [Type]
          | Arrow AnnVar Type Type
          | TyVar Name

-- | A few build-in types.
data BasicType = Integer
               | Char
               | Double

-- | Annotation variable.
type AnnVar = Name

-- | Definition of a custom Haskell98 algebraic data type. May be (non-mutually) recursive, but 
--   must be regular and can not be paramterized.
data DataDef = DataDef {dataName :: Name, ctors :: [DataCon]}

-- | Definition of one constructor within a data type.
data DataCon = DataCon {conName :: Name, members :: [Type]}

-- | Environment of user-defined data types. Also contains a mapping from constructor names to
--   data definition names.
data DataEnv = DataEnv {defs :: Map Name DataDef, conNameMap :: Map Name Name}

-- | Look up the definition of a data type with a certain name.
lookupDataDef :: Name -> DataEnv -> Maybe DataDef
lookupDataDef n = M.lookup n . defs

-- | Look up the data type which contains a constructor with a particular name.
lookUpConSource :: Name -> DataEnv -> Maybe Type
lookUpConSource n = fmap DataType . M.lookup n . conNameMap

-- | Add a data definition to the environment.
addDataDef :: DataDef -> DataEnv -> DataEnv
addDataDef def env = env {defs = M.insert dname def (defs env), conNameMap = addCons $ ctors def}
 where dname = dataName def
       addCons cs = foldr (\(DataCon n _) -> (M.insert n dname .)) id cs $ conNameMap env

-- | A type environment: a mapping from type variable names to the types they represent.
type TyEnv = Map Name Type
