{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Analysis.Inference where

import HaskellControlFlow.Calculus.Calculus
import HaskellControlFlow.Calculus.Types

import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Arrow
import Control.Monad

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
freshVar (VarFactory n) = ('$' : show n, VarFactory $ n + 1)

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
unify :: Monad m => Type -> Type -> AnnConstraints -> m (TySubst, AnnConstraints)
unify a b constraints = case (a, b) of
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
                  f (s1, constraints) (a, b) = do
                      (s2, constraints1) <- unify a b constraints
                      return (s2 . s1, constraints1)
    
    _ -> fail $ concat ["Type error.\n\tExpected: '", show a, "'.\n\tActual: '", show b, "'."]

-- | Unifies annotation variables with constraints.
unifyAnnVars :: Maybe AnnVar -> Maybe AnnVar -> AnnConstraints -> AnnConstraints
unifyAnnVars (Just a) (Just b) constraints = (SubstituteConstraint a b) : constraints
unifyAnnVars _        _        constraints = constraints

-- | Provides the type of a constant literal.
constantType :: Constant -> Type
constantType c = case c of
    IntegerConst _ -> BasicType Integer
    DoubleConst  _ -> BasicType Double
    CharConst    _ -> BasicType Char
    StringConst  _ -> ListType (BasicType Char)

-- | Implements algorithm W for type inference.
algorithmW :: Monad m => VarFactory -> DataEnv -> TyEnv -> AnnConstraints -> Term -> m (Type, TySubst, VarFactory, AnnConstraints)
algorithmW fac defs env constraints term = case term of
    ConstantTerm c ->
         return (constantType c, id, fac, constraints)

    VariableTerm name -> 
        case M.lookup name env of
            Nothing -> fail $ "Not in scope: '" ++ name ++ "'."
            Just ty -> return (ty, id, fac, constraints)

    AbstractionTerm x t1 -> do
        let (a1, fac1) = first TyVar $ freshVar fac
        let (a2, fac2) = freshVar fac1
        
        (ty2, s, fac2, constraints1) <- algorithmW fac2 defs (M.insert x a1 env) constraints t1
        
        return (Arrow (Just a2) (s a1) ty2, s, fac2, constraints1)

    ApplicationTerm t1 t2 -> do
        let (a1, fac1) = first TyVar $ freshVar fac
        let (a2, fac2) = freshVar fac1
        
        (ty1, s1, fac3, constraints1) <- algorithmW fac1 defs env constraints t1
        (ty2, s2, fac4, constraints2) <- algorithmW fac2 defs (M.map s1 env) constraints1 t2
        
        (s3, constraints3) <- unify (s2 ty1) (Arrow (Just a2) ty2 a1) constraints2
        
        return (s3 a1, s3 . s2 . s1, fac4, constraints3)

    LetInTerm (NamedTerm name t1) t2 -> do
        (ty1, s1, fac1, constraints1) <- algorithmW fac defs env constraints t1
        (ty2, s2, fac2, constraints2) <- algorithmW fac1 defs (M.map s1 $ M.insert name (gen (M.map s1 env) ty1) env) constraints1 t2
        
        let constraints3 =
                case ty1 of
                    Arrow (Just a) _ _ -> (InclusionConstraint a name) : constraints2
                    _                  -> constraints2
        
        return (ty2, s2 . s1, fac2, constraints3)

    ListTerm ts -> 
     -- Unify the types of all members of the list literal.
     let inferMember (ty, s1, fac1, constraints) term = do
             (ty1, s2, fac1, constraints1) <- algorithmW fac1 defs (M.map s1 env) constraints term
             (s3, constraints2) <- unify ty ty1 constraints1
             let sx = s3 . s2 . s1
             return (sx ty, sx, fac1, constraints2)
     in case ts of
         []     -> fail "Polymorphism is not supported, so can't infer the empty lists."
         (t:ts) -> do
             first <- algorithmW fac defs env constraints t
             (ty, s, fac1, constraints1) <- foldM inferMember first ts
             return (ListType ty, s, fac1, constraints1)

    TupleTerm ts ->
        -- Similar to inferring lists, but types of members do not have to match.
        let inferMember (tys, s1, fac1, constraints) term = do
                (ty, s2, fac2, constraints1) <- algorithmW fac1 defs (M.map s1 env) constraints term
                let sx = s2 . s1
                return (sx ty : tys, sx, fac2, constraints1)
        in do
            (tys, s, fac1, constraints1) <- foldM inferMember ([], id, fac, constraints) ts
            return (TupleType tys, s, fac1, constraints1)

    CaseTerm t1 pats -> do
        first <- algorithmW fac defs env constraints t1
        
        handlePatterns first pats
        
        where
            handlePatterns _ [] = fail "Empty case statement."
            handlePatterns (ty1, s1, fac1, constraints) ((Variable name, term):_ ) = do
                -- TODO: Put name in environment.
                
                (ty, s2, fac2, constraints1) <- algorithmW fac1 defs (M.map s1 env) constraints term
                return (ty, s2 . s1, fac2, constraints1)

            handlePatterns (ty1, s1, fac1, constraints) ((Pattern name args, term):ps) =
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
                         
                         (ty2, s4, fac2, constraints2) <- algorithmW fac1 defs (M.map sx env1) constraints1 term
                         (ty3, s5, fac3, constraints3) <- if null ps 
                                                          then return (ty2, id, fac1, constraints2) 
                                                          else handlePatterns (ty2, id, fac1, constraints2) ps
                         
                         -- Unify types of different terms.
                         (s6, constraints4) <- unify ty2 ty3 constraints3
                         
                         -- Done.
                         let sy = s6 . s5 . s4 . sx
                         return (sy ty2, sy, fac3, constraints4)

    FixTerm term ->
     do (fty, s, fac1, c1) <- algorithmW fac defs env constraints term

        -- The fixed term should be of type a -> a for some a. After applying the fix operator, the 
        -- resulting type will be a.
        let (ty, fac2) = first TyVar $ freshVar fac1
        (s1, c2) <- unify fty (Arrow Nothing ty ty) c1
        return (s1 ty, s1 . s, fac2, c2)

-- | Constraint solver.
solveAnnConstraints :: AnnConstraints -> AnnEnv
solveAnnConstraints []     = (M.empty, M.empty)
solveAnnConstraints (x:xs) = case x of
    InclusionConstraint var name ->
        let (allNames, substitutions) = solveAnnConstraints xs
        in case M.lookup var substitutions of
            Just subsitute -> insertName subsitute name allNames substitutions
            Nothing        -> insertName var       name allNames substitutions
        where
            insertName var name allNames substitutions = case M.lookup var allNames of
                Just varNames -> (M.insert var (S.insert name varNames) allNames, substitutions)
                Nothing       -> (M.insert var (S.insert name S.empty)  allNames, substitutions)
    
    SubstituteConstraint first second ->
        let (allNames, substitutions) = solveAnnConstraints xs
        in case M.lookup (cannonicalVarName first substitutions) allNames of
            Just _  -> (allNames, insertSubsitution second first substitutions)
            Nothing -> (allNames, insertSubsitution first second substitutions)
        where
            insertSubsitution first second substitutions =
                M.insert first (cannonicalVarName second substitutions) substitutions
            
            cannonicalVarName var substitutions = case M.lookup var substitutions of
                Just substitution -> substitution
                Nothing           -> var

-- | Looks up annotation names in the solved annotations.
lookupAnnNames :: AnnVar -> AnnEnv -> [Name]
lookupAnnNames var (allNames, substitutions) =
    case M.lookup (cannonicalVarName var substitutions) allNames of
        Just namesSet -> S.toList namesSet
        Nothing       -> []
    where
        cannonicalVarName var substitutions = case M.lookup var substitutions of
            Just substitution -> substitution
            Nothing           -> var

-- | Uses algorithmW to find a principal type: the most polymorphic type that can be assigned to a 
--   given term. An environment should be provided and will be updated. Monadic 'fail' is used in 
--   case of a type error. 
inferPrincipalType :: Monad m => Term -> DataEnv -> TyEnv -> m (Type, TyEnv, AnnEnv)
inferPrincipalType term datas env = 
  do (ty, s, _, constraints) <- algorithmW initVarFactory datas env [] term
     let newEnv = M.map s env
     return (gen newEnv ty, newEnv, solveAnnConstraints constraints)
