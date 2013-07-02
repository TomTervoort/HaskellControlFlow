{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Analysis.Inference where

import HaskellControlFlow.Calculus.Calculus
import HaskellControlFlow.Calculus.Types

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Control.Arrow
import Control.Monad

import Debug.Trace

-- | A type substitution. For any `s :: TySubst`, it should hold that `s . s` is equivalent to `s`.
type TySubst = Type -> Type

-- | A type variable.
type TyVar = Name

-- | Generator of fresh names for variables.
newtype VarFactory = VarFactory Int

-- | Initialise a new fresh variable factory.
initVarFactory :: VarFactory
initVarFactory = VarFactory 0

-- | Generate a fresh variable name.
freshVar :: VarFactory -> (Name, VarFactory)
freshVar (VarFactory n) = ("_" ++ show n, VarFactory $ n + 1)

-- | Provides the free type variables within a type.
freeVars :: Type -> Set TyVar
freeVars ty = 
 case ty of
  ListType t    -> freeVars t
  TupleType ts  -> S.unions $ map freeVars ts
  Arrow _ t1 t2 -> freeVars t1 `S.union` freeVars t2
  TyVar v       -> S.singleton v
  other         -> S.empty

-- | Provides the free type variables within a type environment.
freeEnvVars :: TyEnv -> Set TyVar
freeEnvVars = S.unions . map (freeVars . snd) . M.assocs

-- | Type generalisation. (TODO)
gen :: TyEnv -> Type -> Type
gen env ty = ty
    -- For polymorphism: S.foldr Forall ty $ freeVars ty `S.difference` freeEnvVars env

-- | Type instantiation. (TODO)
inst :: VarFactory -> Type -> (Type, VarFactory)
{-- Poly: inst fac (Forall a t) = let (fresh, fac') = freshTyVar fac
                                   in first (subTyVar a $ TyVar fresh) $ inst fac' t --}
inst fac ty = (ty, fac)

-- Substitute one type variable with a type.
subTyVar :: TyVar -> Type -> TySubst
subTyVar from to = sub
 where sub ty = case ty of
                 TyVar v    | v == from -> to
                            | otherwise -> TyVar v
                 {-- Forall a t | from == a -> Forall a t
                            | otherwise -> Forall a $ sub t--}
                 Arrow an t1 t2 -> Arrow an (sub t1) (sub t2)
                 ListType t     -> ListType $ sub t
                 TupleType ts   -> TupleType $ map sub ts
                 other          -> other

-- | Robinson's unification algorithm. Uses Monad 'fail' in case of a type error.
unify :: Monad m => Type -> Type -> m TySubst
unify a b =
 case (a,b) of
  (TyVar a, TyVar b) | a == b -> return id
  (TyVar a1, t2)     | not $ a1 `S.member` freeVars t2 -> return $ subTyVar a1 t2
  (t1, TyVar a2)     | not $ a2 `S.member` freeVars t1 -> return $ subTyVar a2 t1 
  (BasicType x, BasicType y) | x == y -> return id
  (DataType x, DataType y)   | x == y -> return id
  (ListType t1, ListType t2)          -> unify t1 t2
  (Arrow _ t11 t12, Arrow _ t21 t22)  -> do s1 <- unify t11 t21
                                            s2 <- unify (s1 t12) (s1 t22)
                                            return $ s2 . s1
  
  (TupleType ts1, TupleType ts2) | length ts1 == length ts2
                                    -> do ss <- sequence $ zipWith unify ts1 ts2
                                          return $ foldr (.) id ss

  _ -> fail $ concat ["Type error.\n\tExpected: '", show a, "'.\n\tActual: '", show b, "'."]


-- | Provides the type of a constant literal.
constantType :: Constant -> Type
constantType c = case c of
                  IntegerConst _ -> BasicType Integer
                  DoubleConst  _ -> BasicType Double
                  CharConst    _ -> BasicType Char
                  StringConst  _ -> ListType (BasicType Char)
              

-- | Implements algorithm W for type inference.
algorithmW :: Monad m => VarFactory -> DataEnv -> TyEnv -> Term -> m (Type, TySubst, VarFactory)
algorithmW fac defs env term =
 case term of
  ConstantTerm c        -> 
   return (constantType c, id, fac)

  VariableTerm name     -> 
   case M.lookup name env of 
    Nothing -> fail $ "Can not infer type of '" ++ name ++ "'."
    Just ty -> return (ty, id, fac)

  AbstractionTerm x t1  -> 
   do let (a1, fac') = first TyVar $ freshVar fac
      (ty2, s, fac') <- algorithmW fac' defs (M.insert x a1 env) t1
      return (Arrow Nothing (s a1) ty2, s, fac')

  ApplicationTerm t1 t2 -> 
   do let (a, fac') = first TyVar $ freshVar fac
      (ty1, s1, fac') <- algorithmW fac' defs env t1
      (ty2, s2, fac') <- algorithmW fac' defs (M.map s1 env) t2
      s3 <- unify (s2 ty1) (Arrow Nothing ty2 a)
      return (s3 a, s3 . s2 . s1, fac')

  LetInTerm (NamedTerm x t1) t2 -> 
    do (ty1, s1, fac') <- algorithmW fac defs env t1
       (ty,  s2, fac') <- algorithmW fac' defs (M.map s1 $ M.insert x (gen (M.map s1 env) ty1) env) t2
       return (ty, s2 . s1, fac')

  ListTerm ts -> 
   -- Unify the types of all members of the list literal.
   let inferMember (ty, s1, fac') term =
        do (ty', s2, fac') <- algorithmW fac' defs (M.map s1 env) term
           s3 <- unify ty ty'
           let sx = s3 . s2 . s1
           return (sx ty, sx, fac')
    in case ts of
        []     -> fail "Polymorphism is not supported, so can't infer the empty lists."
        (t:ts) -> do first <- algorithmW fac defs env t
                     (ty, s, fac') <- foldM inferMember first ts
                     return (ListType ty, s, fac')

  TupleTerm ts ->
   -- Similar to inferring lists, but types of members do not have to match.
   let inferMember (tys, s1, fac') term =
        do (ty, s2, fac') <- algorithmW fac' defs (M.map s1 env) term
           let sx = s2 . s1
           return (sx ty : tys, sx, fac')
    in do (tys, s, fac') <- foldM inferMember ([], id, fac) ts
          return (TupleType tys, s, fac')

  CaseTerm t1 pats ->
   do (ty1, s1, fac') <- algorithmW fac defs env t1
      return (ty1, s1, fac')
      let handlePatterns [] = fail "Empty case statement."
          handlePatterns ((Variable n,        term):_ ) = 
           do (ty, s2, fac') <- algorithmW fac' defs (M.map s1 env) term
              return (ty, s2 . s1, fac')

          handlePatterns ((Pattern name args, term):ps) =
           case lookUpConTypes name defs of
            Nothing         -> fail $ "Unknown constructor: " ++ name
            Just (cty, ats) -> do -- Unify expression type.
                                  s2 <- unify ty1 cty
                                  -- Introduce constructor argument types.
                                  let s3 = foldr (.) id $ zipWith subTyVar args ats
                                  -- Infer term.
                                  let sx = s3 . s2 . s1
                                  (ty2, s4, fac') <- algorithmW fac' defs (M.map sx env) term
                                  (ty3, s5, fac') <- if null ps 
                                                      then return (ty2, id, fac') 
                                                      else handlePatterns ps
                                  -- Unify types of different terms.
                                  s6 <- unify ty2 ty3
                                  -- Done.
                                  let sy = s6 . s5 . s4 . sx
                                  return (sy ty2, sy, fac')

      handlePatterns pats

-- | Uses algorithmW to find a principal type: the most polymorphic type that can be assigned to a 
--   given term. An environment should be provided and will be updated. Monadic 'fail' is used in 
--   case of a type error. 
inferPrincipalType :: Monad m => Term -> DataEnv -> TyEnv -> m (Type, TyEnv)
inferPrincipalType term datas env = 
  do (ty, s, _) <- algorithmW initVarFactory datas env term
     let newEnv = M.map s env
     return (gen newEnv ty, newEnv)
