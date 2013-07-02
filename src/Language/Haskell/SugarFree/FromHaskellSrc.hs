{-# LANGUAGE Haskell2010 #-}
{-# LANGUAGE FlexibleContexts #-}
-- | Converts from haskell-src:Language.Haskell.Syntax to SugarFree.
module Language.Haskell.SugarFree.FromHaskellSrc where

{-

TODO:

    * Convert literal patterns to guards.

          function literal = expression
          
          ==>
          
          function fresh0 | fresh0 == literal = expression

    * Convert negation patterns to guards.
    
          function -pattern = expression
          
          ==>
          
          function fresh0 | pattern <- negate fresh0 = expression
    
    * Convert irrefutable patterns to let-bindings.

          function ~pattern = expression
          
          ==>
          
          function fresh0 = let pattern = fresh0 in expression

-}

import Control.Applicative
import Data.Foldable (toList)
import Data.Fresh
import Data.Maybe (fromJust)
import Data.Traversable
import Data.Sequence (replicateA)
import Language.Haskell.Syntax
import qualified Data.Text as T
import qualified Language.Haskell.SugarFree.Syntax as Sf

import Util.OnlyValue

type BindValue = Sf.BindName Sf.ValueLevel
type BindType = Sf.BindName Sf.TypeLevel

fromHsModule
    :: (Applicative f, Fresh BindValue f, Fresh BindType f)
    => HsModule -> f (Sf.Module)
fromHsModule (HsModule _ _ _ _ x) = Sf.Module <$> fromHsDecls x

---
fromHsLiteral :: HsLiteral -> Sf.Literal
fromHsLiteral (HsChar       x) = Sf.LitChar x False
fromHsLiteral (HsCharPrim   x) = Sf.LitChar x True
fromHsLiteral (HsString     x) = Sf.LitString (T.pack x) False
fromHsLiteral (HsStringPrim x) = Sf.LitString (T.pack x) True
fromHsLiteral (HsInt        x) = Sf.LitInt x False
fromHsLiteral (HsIntPrim    x) = Sf.LitInt x True
fromHsLiteral (HsFrac       x) = Sf.LitFrac x Sf.NotFracPrim
fromHsLiteral (HsFloatPrim  x) = Sf.LitFrac x Sf.FracPrimFloat
fromHsLiteral (HsDoublePrim x) = Sf.LitFrac x Sf.FracPrimDouble

---
fromHsDecls
    :: (Applicative f, Fresh BindValue f, Fresh BindType f)
    => [HsDecl] -> f [Sf.Declaration]
fromHsDecls decls = concat . concat <$> sequenceA ((\f -> traverse f decls) <$> [hsToDataDecl, hsToSignDecl, hsToExprDecl])
  where
    hsToDataDecl, hsToSignDecl, hsToExprDecl
        :: (Applicative f, Fresh BindValue f, Fresh BindType f)
        => HsDecl -> f [Sf.Declaration]

    hsToDataDecl x_ = case x_ of
        HsDataDecl _ ctxt name args cons _ ->
            pure [Sf.DataDecl (bindType name) Nothing (map (fromHsConDecl name args) cons)]
        HsNewTypeDecl loc ctxt name args con derivs ->
            hsToDataDecl (HsDataDecl loc ctxt name args [con] derivs)
        _ -> pure []

    fromHsConDecl :: HsName -> [HsName] -> HsConDecl -> (Sf.ConstructorDecl)
    fromHsConDecl tname targs (HsConDecl _ name bt) =
        Sf.ConstructorDecl (bindValue name) (Sf.curryFunctionType (map fromHsBangType bt, mkTypeWithArgs (UnQual tname) targs))
    fromHsConDecl _ _ (HsRecDecl _ _ _) = recordsNotImplementedError

    fromHsBangType :: HsBangType -> Sf.TypeExpr
    fromHsBangType (HsBangedTy ty) = fromHsType ty
    fromHsBangType (HsUnBangedTy ty) = fromHsType ty

    hsToSignDecl x_ = case x_ of
        HsTypeSig _ names qtype ->
            pure $ map (\n -> Sf.SignatureDecl (bindValue n) (fromHsQualType qtype)) names
        _ -> pure []

    {-
    hsToExprDecl (filter 
         HsFunBind     [HsMatch]
         HsPatBind     loc HsPat HsRhs {-where-} [HsDecl]
         -->
         ExprDecl l (BindName ValueLevel) (ValueExpr l)
    -}
    hsToExprDecl x_ = case x_ of
        HsFunBind matches ->
            let names = map (\(HsMatch _ n _ _ _) -> n) $ matches
                args = (\n -> toList $ replicateA n fresh) $ fromJust (error "HsFunBind with multiple arities") $ map (\(HsMatch _ _ a _ _) -> length a) $ matches
                name = fromJust (error "HsFunBind with multiple names") $ onlyValueFrom names
                loc = undefined
                alts = map (\(HsMatch l _ ps r d) -> HsAlt l (HsPTuple ps) (rhsToGuardedAlts r) d) $ matches
                rhs args_ = HsUnGuardedRhs (HsLambda loc (lpat args_) (HsCase (scrt args_) alts))
                lpat = HsPTuple . map HsPVar
                scrt = HsTuple . map (HsVar . useBindV)
            in (\args' -> hsToExprDecl (HsPatBind loc name (rhs args') [])) <$> args
        HsPatBind _ _ _ _ -> pure []
        _ -> pure []

mkTypeWithArgs :: HsQName -> [HsName] -> Sf.TypeExpr
mkTypeWithArgs hd tls
  = let combine acc tl = Sf.ApplyT acc (mk (UnQual tl))
        mk = Sf.UseT . useType
    in foldl combine (mk hd) tls

rhsToGuardedAlts :: HsRhs -> HsGuardedAlts
rhsToGuardedAlts (HsUnGuardedRhs expr) = HsUnGuardedAlt expr
rhsToGuardedAlts (HsGuardedRhss grhss) = HsGuardedAlts (map ff grhss)
  where
    ff (HsGuardedRhs x y z) = HsGuardedAlt x y z

guardedAltsToRhs :: HsGuardedAlts -> HsRhs
guardedAltsToRhs (HsUnGuardedAlt expr) = HsUnGuardedRhs expr
guardedAltsToRhs (HsGuardedAlts grhss) = HsGuardedRhss (map ff grhss)
  where
    ff (HsGuardedAlt x y z) = HsGuardedRhs x y z

--- Expressions
fromHsExp
    :: (Applicative f, Fresh BindValue f, Fresh BindType f)
    => HsExp -> f (Sf.ValueExpr)
fromHsExp expr_ = case expr_ of
    -- pure sugar
    HsInfixApp lhs op rhs   -> fromHsExp (HsApp (HsApp (op2var op) lhs) rhs)
    HsParen expr            -> fromHsExp expr

    -- special functions
    HsTuple exprs -> applySToMany (Sf.HwTupleValue . length $ exprs) exprs
    HsList exprs ->
        foldr applyListCon applyListNil
        <$> traverse fromHsExp exprs
    HsIf cond exprT exprF ->
        (\condX trueX falseX -> Sf.Match . Sf.Destruct condX $
            [ (truePattern, Sf.Accept trueX)
            , (falsePattern, Sf.Accept falseX)
            ])
        <$> fromHsExp cond <*> fromHsExp exprT <*> fromHsExp exprF

    -- hardcoded functions
    HsNegApp expr           -> applySToMany Sf.HwNegate [expr]
    HsEnumFrom eL           -> applySToMany Sf.HwEnumFrom [eL]
    HsEnumFromTo eL eR      -> applySToMany Sf.HwEnumFromTo [eL, eR]
    HsEnumFromThen eL eT    -> applySToMany Sf.HwEnumFromThen [eL, eT]
    HsEnumFromThenTo eL eT eR -> applySToMany Sf.HwEnumFromThenTo [eL, eT, eR]

    -- more complicated sugar
    HsLeftSection lhs op    -> leftSection <$> fromHsExp lhs <*> fromHsExp (op2var op) <*> fresh
    HsRightSection op rhs   -> rightSection <$> fresh <*> fromHsExp (op2var op) <*> fromHsExp rhs

    -- normal
    HsVar name              -> pure . Sf.Use . useValue $ name
    HsCon name              -> pure . Sf.Use . useValue $ name
    HsLit literal           -> Sf.Literal <$> pure (fromHsLiteral literal)
    HsApp lhs rhs           -> Sf.Apply <$> fromHsExp lhs <*> fromHsExp rhs
    -- HsLambda _ patts exp    -> ...
    HsLet decls exp ->
        (\decls' exp' -> foldl (\expr' decl' -> Sf.Declare decl' expr') exp' decls')
        <$> fromHsDecls decls <*> fromHsExp exp
    HsCase exp alts         -> (\exp' alts' -> Sf.Match $ Sf.Destruct exp' alts')
                               <$> fromHsExp exp <*> fromHsAlts alts
    HsExpTypeSig _ vX tX    -> Sf.Signature (fromHsQualType tX) <$> fromHsExp vX

    -- unsupported
    HsDo _          -> comprehensionsNotImplementedError
    HsRecConstr _ _ -> recordsNotImplementedError
    HsRecUpdate _ _ -> recordsNotImplementedError
    HsListComp _ _  -> comprehensionsNotImplementedError
  where
    op2var (HsQVarOp qn) = HsVar qn
    op2var (HsQConOp qn) = HsVar qn

    applySToMany cons exprs = foldl (Sf.Apply) (Sf.Use . Sf.UseHardwired $ cons) <$> traverse fromHsExp exprs

    leftSection lhs op rhsB = Sf.Abstract rhsB $ Sf.Apply (Sf.Apply op lhs) (useBindV rhsB)
    rightSection lhsB op rhs = Sf.Abstract lhsB $ Sf.Apply (Sf.Apply op (useBindV lhsB)) rhs
    applyListCon x xs = Sf.Apply (Sf.Apply (Sf.Use . Sf.UseHardwired $ Sf.HwListCons) x) xs
    applyListNil = Sf.Use . Sf.UseHardwired $ Sf.HwListNil

    truePattern, falsePattern :: Sf.Patt
    truePattern = Sf.Constructor (Sf.UseHardwired Sf.HwTrue) []
    falsePattern = Sf.Constructor (Sf.UseHardwired Sf.HwFalse) []

useBindV :: BindValue -> Sf.ValueExpr
useBindV Sf.Blank = error "trying to use a wildcard as if it binds a variable"
useBindV (Sf.BindName i) = Sf.Use (Sf.UseName i)
useBindV (Sf.BindFresh i) = Sf.Use (Sf.UseFresh i)

useBindT :: BindType -> Sf.TypeExpr
useBindT Sf.Blank = error "trying to use a wildcard as if it binds a variable"
useBindT (Sf.BindName i) = Sf.UseT (Sf.UseName i)
useBindT (Sf.BindFresh i) = Sf.UseT (Sf.UseFresh i)

fromHsAlts
    :: (Applicative f, Fresh BindValue f, Fresh BindType f)
    => [HsAlt] -> f [(Sf.Patt, Sf.Matching)]
fromHsAlts alts = concat <$> traverse fromHsAlt alts
  where
    fromHsAlt (HsAlt _ patt galts [])
      = (\x y -> (,) x <$> y) <$> fromHsPat patt <*> fromHsGuardedAlts galts
    -- TODO fromHsAlt (HsAlt _ _ _ (_:_))

fromHsGuardedAlts
    :: (Applicative f, Fresh BindValue f, Fresh BindType f)
    => HsGuardedAlts -> f [Sf.Matching]
fromHsGuardedAlts (HsUnGuardedAlt exp) = (:[]) . Sf.Accept <$> fromHsExp exp
fromHsGuardedAlts (HsGuardedAlts galts) = traverse unGuardedAlt galts
  where
    unGuardedAlt
        :: (Applicative f, Fresh BindValue f, Fresh BindType f)
        => HsGuardedAlt -> f (Sf.Matching)
    unGuardedAlt (HsGuardedAlt _ gexp vexp)
      = (\gg vv -> Sf.Destruct gg [
            (Sf.Constructor (Sf.UseHardwired Sf.HwTrue) [], Sf.Accept vv)
            ])
        <$> fromHsExp gexp <*> fromHsExp vexp

--- Patterns 

fromHsPat
    :: (Applicative f, Fresh BindValue f)
    => HsPat -> f Sf.Patt
fromHsPat patt_ = case patt_ of
    -- pure sugar
    HsPInfixApp lhs cons rhs -> fromHsPat (HsPApp cons [lhs, rhs])
    HsPList [] -> pure $ Sf.Constructor (Sf.UseHardwired Sf.HwListNil) []
    HsPList patts ->
        let consPatt x y = HsPApp (Special HsCons) [x, y]
            nilPatt = HsPList []
        in fromHsPat (foldr consPatt nilPatt patts)
    HsPTuple patts ->
        let constructor = Special (HsTupleCon (length patts))
        in fromHsPat (HsPApp constructor patts)
    HsPParen patt -> fromHsPat patt
    -- complicated sugar is not yet supported
    HsPVar name -> Sf.Alias (bindValue name) <$> pure (Sf.Whatever)
    HsPApp cons patts -> Sf.Constructor (useValue cons) <$> traverse fromHsPat patts
    HsPAsPat name patt -> Sf.Alias (bindValue name) <$> fromHsPat patt
    HsPWildCard -> pure (Sf.Whatever)
    -- Unsupported!
    HsPLit literal -> complicatedPatternError
    HsPNeg patt -> complicatedPatternError
    HsPIrrPat patt -> complicatedPatternError
    HsPRec _ _ -> recordsNotImplementedError

---

fromHsQualType :: HsQualType -> Sf.TypeExpr
fromHsQualType (HsQualType ctxt ty) = fromHsType ty {- TODO fromHsContext ctxt -}

fromHsType :: HsType -> Sf.TypeExpr
fromHsType ty_ = case ty_ of
    -- pure sugar
    HsTyFun lhs rhs ->
        Sf.ApplyT (Sf.ApplyT (Sf.UseT . Sf.UseHardwired $ Sf.HwFunctionType) (fromHsType lhs)) (fromHsType rhs)
    HsTyTuple types ->
        foldl (Sf.ApplyT) (Sf.UseT . Sf.UseHardwired . Sf.HwTupleType $ length types) (map fromHsType types)

    -- normal
    HsTyApp lhs rhs -> Sf.ApplyT (fromHsType lhs) (fromHsType rhs)
    HsTyVar name -> Sf.UseT . useType . UnQual $ name
    HsTyCon name -> Sf.UseT . useType $ name

fromHsContext :: HsContext -> [Sf.TypeExpr]
fromHsContext = map fromHsAsst
  where
    fromHsAsst (cn, tys) = foldr (Sf.ApplyT) (Sf.UseT (useType cn)) (map fromHsType tys)

---

makeIdentifier :: Maybe Module -> HsName -> Sf.Identifier p
makeIdentifier mm nn
  = let mm' = fromHsModuleName mm
        (tt', nn') = case nn of
            HsIdent x -> (Sf.Wordy, T.pack x)
            HsSymbol x -> (Sf.Symbolic, T.pack x)
    in Sf.Identifier mm' tt' nn'

bindValue :: HsName -> BindValue
bindValue = Sf.BindName . makeIdentifier Nothing

bindType :: HsName -> BindType
bindType = Sf.BindName . makeIdentifier Nothing

useValue :: HsQName -> Sf.UseName Sf.ValueLevel
useValue (Qual m n) = Sf.UseName . makeIdentifier (Just m) $ n
useValue (UnQual x) = useValue (Qual (Module []) x)
useValue (Special x) = fromSpecialValue x

useType :: HsQName -> Sf.UseName Sf.TypeLevel
useType (Qual m n) = Sf.UseName . makeIdentifier (Just m) $ n
useType (UnQual x) = useType (Qual (Module []) x)
useType (Special x) = fromSpecialType x

fromSpecialValue :: HsSpecialCon -> Sf.UseName Sf.ValueLevel
fromSpecialValue HsUnitCon = Sf.UseHardwired (Sf.HwTupleValue 0)
fromSpecialValue HsListCon = error "list type constructor on value level"
fromSpecialValue HsFunCon = error "function type constructor on value level"
fromSpecialValue (HsTupleCon x) = Sf.UseHardwired (Sf.HwTupleValue x)
fromSpecialValue HsCons = Sf.UseHardwired Sf.HwListCons

fromSpecialType :: HsSpecialCon -> Sf.UseName Sf.TypeLevel
fromSpecialType HsUnitCon = Sf.UseHardwired (Sf.HwTupleType 0)
fromSpecialType HsListCon = Sf.UseHardwired Sf.HwListType
fromSpecialType HsFunCon = Sf.UseHardwired Sf.HwFunctionType
fromSpecialType (HsTupleCon x) = Sf.UseHardwired (Sf.HwTupleType x)
fromSpecialType HsCons = error "list 'cons' constructor on type level"

fromHsModuleName :: Maybe Module -> Sf.Qualification
fromHsModuleName Nothing = Sf.Unqualified
fromHsModuleName (Just (Module xs)) = Sf.Qualified . T.splitOn (T.singleton '.') . T.pack $ xs

-- Error messages

recordsNotImplementedError = error "unimplemented syntax (records)"
comprehensionsNotImplementedError = error "unimplemented syntax (do-notation, list comprehensions)"
complicatedPatternError = error "unimplemented syntax (complicated patterns)"
