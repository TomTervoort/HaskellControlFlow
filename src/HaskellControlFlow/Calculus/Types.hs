{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Types where

import HaskellControlFlow.Calculus.Calculus

import Data.Map (Map)
import qualified Data.Map as M

-- | A Haskell type. May also contain function type annotations or type variables.
--   Since lists and tuples are parametrized and can therefore not be generally defined in the 
--   subset of Haskell we support, they are considered as special cases.
data Type = BasicType BasicType
          | DataType Name
          | ListType Type
          | TupleType [Type]
          | Arrow (Maybe AnnVar) Type Type
          | TyVar Name
          -- | Forall Name Type (polymorphism)
           deriving (Show)

-- | A few build-in types.
data BasicType = Integer
               | Char
               | Double
                 deriving (Eq, Show)

-- | Annotation variable.
type AnnVar = Name

-- | A type environment: a mapping from variable names to their inferred types.
type TyEnv = Map Name Type

-- | An environment of types of standard functions such as arithmetic operators.
initTyEnv :: TyEnv
initTyEnv = M.fromList stdOps
 where stdOps = [] -- TODO

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
data DataEnv = DataEnv {defs :: Map Name DataDef, conNameMap :: Map Name Name}

-- | Initial environment containing solely the bool type.
initEnv :: DataEnv
initEnv = addDataDef boolDef $ DataEnv M.empty M.empty

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

-- | Update a type environment with the type signatures for constructors used within a DataEnv so 
--   those can be treated as functions.
constructorTypes :: DataEnv -> TyEnv -> TyEnv
constructorTypes env = foldr (.) id $ concatMap (conTypes . snd) $ M.assocs $ defs env
 where conTypes (DataDef dname ctors) = map (\(DataCon n ms) -> M.insert n (mkFunc ms dname)) ctors
       mkFunc ins out = foldr (Arrow Nothing) (DataType out) ins
