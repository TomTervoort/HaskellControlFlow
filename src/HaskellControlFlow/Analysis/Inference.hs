{-# LANGUAGE Haskell2010 #-}
{-# LANGUAGE FlexibleContexts #-}

module HaskellControlFlow.Analysis.Inference where

import HaskellControlFlow.Calculus.Calculus
import HaskellControlFlow.Calculus.Types
import HaskellControlFlow.Analysis.CfaSolver

import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad

import Data.Fresh
import Data.Functor

-- | A type substitution. For any `s :: TySubst`, it should hold that `s . s` is equivalent to `s`.
type TySubst = Type -> Type

-- | A type variable.
type TyVar = Name

-- | Generate a fresh variable name.
freshVar :: (Functor m, Fresh m Integer) => m Name
freshVar = fmap (\n -> '$' : show (n :: Integer)) fresh

-- | Provides the free type variables within a type.
freeVars :: Type -> Set TyVar
freeVars ty = 
 case ty of
  ListType t    -> freeVars t
  TupleType ts  -> S.unions $ map freeVars ts
  Arrow _ t1 t2 -> freeVars t1 `S.union` freeVars t2
  TyVar v       -> S.singleton v
  _             -> S.empty

-- | Provides the free type variables within a type environment.
freeEnvVars :: TyEnv -> Set TyVar
freeEnvVars = S.unions . map (freeVars . snd) . M.assocs

-- | Type generalisation. (TODO)
gen :: TyEnv -> Type -> Type
gen _ ty = ty
    -- For polymorphism: S.foldr Forall ty $ freeVars ty `S.difference` freeEnvVars env

-- | Type instantiation. (TODO)
inst :: (Fresh m Integer, Monad m) => Type -> m Type
{-- Poly: inst fac (Forall a t) = let (fresh, fac') = freshTyVar fac
                                   in first (subTyVar a $ TyVar fresh) $ inst fac' t --}
inst ty = return ty

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
unify :: Monad m => Type -> Type -> AnnConstraints -> m (TySubst, AnnConstraints)
unify a_ b_ constraints = case (a_, b_) of
    (TyVar a, TyVar b) | a == b -> return (id, constraints)
    (TyVar a1, t2)     | not $ a1 `S.member` freeVars t2 -> return (subTyVar a1 t2, constraints)
    (t1, TyVar a2)     | not $ a2 `S.member` freeVars t1 -> return (subTyVar a2 t1, constraints)
    (BasicType x, BasicType y) | x == y -> return (id, constraints)
    (DataType x, DataType y)   | x == y -> return (id, constraints)
    (ListType t1, ListType t2)          -> unify t1 t2 constraints
    (Arrow a1 t11 t12, Arrow a2 t21 t22) -> do
        (s1, constraints1) <- unify t11 t21 constraints
        (s2, constraints2) <- unify (s1 t12) (s1 t22) constraints1
        
        let constraints3 = unifyAnnVars a1 a2 constraints2
        
        return (s2 . s1, constraints3)
    
    (TupleType ts1, TupleType ts2) | length ts1 == length ts2 -> do
        foldM f (id, constraints) $ zip ts1 ts2
              where
                  f (s1, cs) (a, b) = do
                      (s2, cs') <- unify a b cs
                      return (s2 . s1, cs')
    
    _ -> fail $ concat ["Type error.\n\tExpected: '", show a_, "'.\n\tActual: '", show b_, "'."]

-- | Unifies annotation variables with constraints.
unifyAnnVars :: Maybe AnnVar -> Maybe AnnVar -> AnnConstraints -> AnnConstraints
unifyAnnVars (Just a) (Just b) constraints = (SubstituteConstraint a b) : constraints
unifyAnnVars _        _        constraints = constraints

-- | Provides the type of a constant literal.
constantType :: Literal -> Type
constantType c = case c of
    IntegerLit  _ -> BasicType Integer
    RationalLit _ -> BasicType Double
    CharLit     _ -> BasicType Char
    StringLit   _ -> ListType (BasicType Char)

-- | Implements algorithm W for type inference.
algorithmW :: (Fresh m Integer, Functor m, Monad m) => DataEnv -> TyEnv -> AnnConstraints -> Term (Maybe Name, Type) ->
    m (Term Type, TySubst, AnnConstraints)
algorithmW defs env constraints term = case term of
    LiteralTerm _ c ->
         return (constantType c <$ term, id, constraints)

    VariableTerm _ name -> 
        case M.lookup name env of
            Nothing -> fail $ "Not in scope: '" ++ name ++ "'."
            Just ty -> return (ty <$ term, id, constraints)

    HardwiredTerm _ (HwTupleCon n) -> do
        argTypes <- map TyVar <$> replicateM n freshVar
        ann1 <- freshVar
        ann2 <- freshVar
        let annText1 = "(" ++ replicate n ',' ++ ")"
        let annText2 = "{inside " ++ annText1 ++ "}"

        let resultType = TupleType argTypes
        let termType = foldr (Arrow (Just ann2)) resultType argTypes

        let (termType', constraints') = case termType of
                Arrow _ fstTy moreTy ->
                    ( Arrow (Just ann1) fstTy moreTy
                    , InclusionConstraint ann1 annText1
                    : InclusionConstraint ann2 annText2
                    : constraints)
                _ -> (termType, constraints)

        return (termType' <$ term, id, constraints')

    HardwiredTerm _ HwListCons -> do
        ty <- TyVar <$> freshVar
        ann1 <- freshVar
        ann2 <- freshVar
        let annText1 = "(:)"
        let annText2 = "{inside " ++ annText1 ++ "}"

        let constraints' =
                ( InclusionConstraint ann1 annText1
                : InclusionConstraint ann2 annText2
                : constraints)

        let termType = Arrow (Just ann1) ty (Arrow (Just ann2) (ListType ty) (ListType ty))
        return (termType <$ term, id, constraints')

    HardwiredTerm _ HwListNil -> do
        ty <- TyVar <$> freshVar
        let termType = ListType ty
        return (termType <$ term, id, constraints)

    AbstractionTerm (enName, _enType) name t1 -> do
        a1 <- TyVar <$> freshVar

        let env1 = M.insert name a1 env
        
        (tt1, s, constraints1) <- algorithmW defs env1 constraints t1
        
        let termType  = Arrow enName (s a1) (annotation tt1)
        let typedTerm = AbstractionTerm termType name tt1
        
        return (typedTerm, s, constraints1)

    ApplicationTerm _ t1 t2 -> do
        a1 <- TyVar <$> freshVar
        a2 <- freshVar
        
        (tt1, s1, constraints1) <- algorithmW defs env constraints t1
        (tt2, s2, constraints2) <- algorithmW defs (M.map s1 env) constraints1 t2
        
        (s3, constraints3) <- unify (s2 $ annotation tt1) (Arrow (Just a2) (annotation tt2) a1) constraints2
        
        let termType  = s3 a1
        let typedTerm = ApplicationTerm termType tt1 tt2
        
        return (typedTerm, s3 . s2 . s1, constraints3)

    LetInTerm _ name t1 t2 -> do
        a1 <- freshVar
        
        (tt1, s1, constraints1) <- algorithmW defs env constraints t1
        
        let newType =
                case annotation tt1 of
                        Arrow _ from to -> Arrow (Just a1) from to
                        x               -> x
        
        let env1 = M.map s1 $ M.insert name (gen (M.map s1 env) newType) env
        
        (tt2, s2, constraints2) <- algorithmW defs env1 constraints1 t2
        
        let constraints3 =
                case annotation tt1 of
                    Arrow (Just a2) _ _ -> (InclusionConstraint a1 name) : (SubstituteConstraint a1 a2) : constraints2
                    Arrow Nothing _ _   -> (InclusionConstraint a1 name) : constraints2
                    _                   -> constraints2
        
        let termType  = annotation tt2
        let typedTerm = LetInTerm termType name (const newType `shallowMapAnnotation` tt1) tt2
        
        return (typedTerm, s2 . s1, constraints3)

    CaseTerm _ t1 patterns -> do
        (tt, s1, constaints1) <- algorithmW defs env constraints t1
        
        (ty, s2, constaints2, typedAlts) <- handlePatterns defs env (annotation tt, s1, constaints1) patterns
        
        let termType  = ty
        let typedTerm = CaseTerm termType tt typedAlts
        
        return (typedTerm, s2, constaints2)

    FixTerm _ t -> do
        a1 <- freshVar
        (fty, s, c1) <- algorithmW defs env constraints t
        
        -- The fixed term should be of type a -> a for some a. After applying the fix operator, the 
        -- resulting type will be a.
        ty <- TyVar <$> freshVar
        
        (s1, c2) <- unify (annotation fty) (Arrow (Just a1) ty ty) c1
        
        let termType  = s1 ty
        let typedTerm = FixTerm termType fty
        
        return (typedTerm, s1 . s, c2)

handlePatterns :: (Monad m, Functor m, Fresh m Integer)
    => DataEnv -> M.Map Name Type -> (Type, Type -> Type, AnnConstraints) -> [(Pattern, Term (Maybe Name, Type))]
    -> m (Type, Type -> Type, AnnConstraints, [(Pattern, Term Type)])
handlePatterns _ _ _ [] = fail "Empty case statement."
handlePatterns defs env (ty1, s1, constraints) ((p@(Variable name), pTerm):_ ) = do
    let env1 = M.map s1 $ M.insert name (gen (M.map s1 env) ty1) env
    
    (tt, s2, constraints1) <- algorithmW defs env1 constraints pTerm
    
    return (annotation tt, s2 . s1, constraints1, [(p, tt)])

handlePatterns defs env (ty1, s1, constraints) ((p@(Pattern name args), pTerm):ps) =
     case lookUpConTypes name defs of
         Nothing         -> fail $ "Unknown constructor: " ++ name
         Just (cty, ats) -> do
             -- Unify expression type.
             (s2, constraints1) <- unify ty1 cty constraints
             
             -- Introduce constructor argument types.
             let s3   = foldr (.) id $ zipWith subTyVar args ats
             let env1 = foldr (uncurry M.insert) env $ zip args ats
             
             -- Infer term.
             let sx = s3 . s2 . s1
             
             let env2 = M.map sx env1
             
             (tt, s4, constraints2) <- algorithmW defs env2 constraints1 pTerm
             (ty3, s5, constraints3, typedAlts) <-
                 if null ps 
                 then return (annotation tt, id, constraints2, []) 
                 else handlePatterns defs env (ty1, id, constraints2) ps
             
             -- Unify types of different terms.
             (s6, constraints4) <- unify (annotation tt) ty3 constraints3
             
             -- Done.
             let sy = s6 . s5 . s4 . sx
             return (sy (annotation tt), sy, constraints4, (p, tt) : typedAlts)

-- | Updates a type environment with the type signatures for constructors used within a DataEnv so 
--   those can be treated as functions.
constructorTypes :: (Fresh m Integer, Functor m, Monad m) => DataEnv -> TyEnv -> AnnConstraints -> m (TyEnv, AnnConstraints)
constructorTypes dataEnv env_ constraints_ = do
    let dataDefs = map snd $ M.assocs $ ddefs dataEnv
    
    foldM addDataDefs (env_, constraints_) dataDefs
        where
            addDataDefs (env, constraints) (DataDef dName cs) = do
                (env1, constraints1, _) <- foldM addDataCons (env, constraints, dName) cs
                return (env1, constraints1)
                
            addDataCons (env, constraints, dName) (DataCon cName args) = do
                a1 <- freshVar
                
                let constraints1 = (InclusionConstraint a1 cName) : constraints
                
                let ty   = constructType (Just a1) dName args
                let env1 = M.insert cName ty env
                
                return (env1, constraints1, dName)
                
            constructType var dName (m:ms) = Arrow var m (constructType Nothing dName ms)
            constructType _   dName []     = DataType dName

-- | Uses algorithmW to find a principal type: the most polymorphic type that can be assigned to a 
--   given term. An environment should be provided and will be updated. Monadic 'fail' is used in 
--   case of a type error. 
inferPrincipalType :: (Fresh m Integer, Functor m, Monad m) => Term (Maybe Name, Type) -> DataEnv -> m (Type, Term Type, AnnEnv)
inferPrincipalType term denv = do
    let constraints = []
    -- TODO initialize (Fresh m Integer, Fresh m AnnVar) here
    let env         = initTyEnv
    
    (env1, constraints1) <- constructorTypes denv env constraints
    
    (tt, s, constraints2) <- algorithmW denv env1 constraints1 term
    
    let newEnv = M.map s env
    
    return (gen newEnv $ annotation tt, fmap s tt, solveAnnConstraints constraints2)
