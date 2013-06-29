{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Parser.Parser (parseHaskellFile) where

import HaskellControlFlow.Calculus.Calculus
import HaskellControlFlow.Calculus.Types

import Language.Haskell.Parser
import Language.Haskell.Syntax

import Data.Either

-- | Parses a haskell file.
parseHaskellFile :: FilePath -> IO HaskellProgram
parseHaskellFile filename = do
    -- Read file contents.
    contents <- readFile filename
    
    -- Parse module.
    return $ case parseModuleWithMode (ParseMode {parseFilename = filename}) contents of
        ParseOk hsModule -> parseHaskellModule hsModule
        ParseFailed (SrcLoc {srcLine = line, srcColumn = column}) message ->
            error $ filename ++ (':' : show line) ++ (':' : show column) ++ (':' : message)

-- | Parses a module.
parseHaskellModule :: HsModule -> HaskellProgram
parseHaskellModule (HsModule _ _ _ _ declarations) =
    let (defs, lets) = partitionEithers $ concatMap parseDeclaration declarations
     in HaskellProgram {datatypes = foldr addDataDef initEnv defs,
                        topExpr = multipleLets lets (VariableTerm {varName = "main"})}

-- | Parses a data or function declaration.
parseDeclaration :: HsDecl -> [Either DataDef NamedTerm]
parseDeclaration declaration = case declaration of
    HsTypeDecl _ _ _ _ -> error "Type synonyms not supported."
    HsTypeSig _ _ _    -> [] -- We ignore type signatures and infer everything ourselves.
    
    HsDataDecl _ _ name params constructors _
     | not $ null params -> error "Parametrized data type declarations are not supported."
     | otherwise         -> [Left $ DataDef {dataName = parseName name, ctors = map parseDataCon constructors}]
    
    HsPatBind _ pattern rhs whereDeclarations ->
        [Right $ NamedTerm {name = parseNamePattern pattern, term = parseLambda [] rhs whereDeclarations}]
    
    HsFunBind [HsMatch _ name patterns rhs whereDeclarations] ->
        [Right $ NamedTerm {name = parseName name, term = parseLambda patterns rhs whereDeclarations}]
    
    -- Unsuported features.
    HsFunBind _                 -> error "Pattern matching within functions not supported. Use case instead"
    HsNewTypeDecl _ _ _ _ _ _   -> error "New type notation not supported."
    HsClassDecl _ _ _ _ _       -> error "Class notation not supported."
    HsInfixDecl _ _ _ _         -> error "Infix notation not supported."
    HsInstDecl _ _ _ _ _        -> error "Instance notation not supported."
    HsDefaultDecl _ _           -> error "Default notation not supported."
    HsForeignImport _ _ _ _ _ _ -> error "Foreign import not supported."
    HsForeignExport _ _ _ _ _   -> error "Foreign export not supported."

-- | Parses an expression.
parseExpression :: HsExp -> Term
parseExpression expr = case expr of    
    HsVar name ->
        VariableTerm {varName = parseQName name}
        
    HsCon name ->
        VariableTerm {varName = parseQName name}
    
    HsLit literal ->
        parseLiteral literal
    
    HsApp lhsExpr rhsExpr ->
        ApplicationTerm {lhsTerm = parseExpression lhsExpr
                        ,rhsTerm = parseExpression rhsExpr}
    
    HsLambda _ patterns bodyExpr -> parseLambda patterns (HsUnGuardedRhs bodyExpr) []
    
    HsLet letDeclarations inExpr ->
        multipleLets (concatMap (rights . parseDeclaration) letDeclarations) 
                     (parseExpression inExpr)
    
    HsIf firstExpr thenExpr elseExpr ->
        CaseTerm {exprTerm = parseExpression firstExpr,
                  alts     = [
                              (Pattern "True" [],  parseExpression thenExpr),
                              (Pattern "False" [], parseExpression elseExpr)
                             ]}
    
    HsParen subExpr          -> parseExpression subExpr
    HsExpTypeSig _ subExpr _ -> parseExpression subExpr
    
    HsInfixApp l op r       -> 
        ApplicationTerm {lhsTerm = ApplicationTerm (parseOperator op) (parseExpression l)
                        ,rhsTerm = parseExpression r}

    HsNegApp subExpr -> 
        ApplicationTerm (VariableTerm "negate") $ parseExpression subExpr

    HsCase expr alternatives -> 
     CaseTerm {exprTerm = parseExpression expr,
               alts     = map parseCaseAlternative alternatives}

    HsTuple values -> 
     TupleTerm $ map parseExpression values
    HsList values -> 
     ListTerm $ map parseExpression values

    -- Unsuported features.
    HsDo _                 -> error "Do notation not supported."
    HsLeftSection _ _      -> error "Left section supported."
    HsRightSection _ _     -> error "Right section not supported."
    HsRecConstr _ _	       -> error "Record notation not supported."
    HsRecUpdate _ _        -> error "Record notation not supported."
    HsEnumFrom _	       -> error "Enum notation not supported."
    HsEnumFromTo _ _       -> error "Enum notation not supported."	
    HsEnumFromThen _ _	   -> error "Enum notation not supported."
    HsEnumFromThenTo _ _ _ -> error "Enum notation not supported."
    HsListComp _ _	       -> error "List comprehensions not supported."
    
    HsAsPat _ _ -> error "Pattern matching supported within case alternatives."
    HsWildCard  -> error "Pattern matching supported within case alternatives."
    HsIrrPat _  -> error "Pattern matching supported within case alternatives."

-- | Parses a literal (constant) value.
parseLiteral :: HsLiteral -> Term
parseLiteral literal = case literal of
    HsChar char	    -> ConstantTerm {constant = CharConst char}
    HsString string	-> ConstantTerm {constant = StringConst string}
    HsInt integer   -> ConstantTerm {constant = IntegerConst integer}
    HsFrac rational	-> ConstantTerm {constant = DoubleConst rational}
    
    -- Unsuported features.
    _ -> error "Unboxed literals are not supported."

-- | Parses a qualified name.
parseQName :: HsQName -> Name
parseQName qName = case qName of
    UnQual name -> parseName name

    -- Unsuported features.
    Qual _ _  -> error "Qualified names are not supported."
    Special c -> error "Special constructors are not supported."

-- | Parses a name.
parseName :: HsName -> Name
parseName fullName = case fullName of
    HsIdent name  -> name
    HsSymbol name -> name

-- | Parses a lambda expression.
parseLambda :: [HsPat] -> HsRhs -> [HsDecl] -> Term
parseLambda patterns rhs whereDeclarations = 
    foldr (\arg term -> AbstractionTerm {argName = arg, bodyTerm = term}) bodyTerm arguments
        where
            arguments = map parseNamePattern patterns
            bodyTerm  = case whereDeclarations of
                [] -> parseRightHandSide rhs
                _  -> multipleLets (concatMap (map nodata . parseDeclaration) whereDeclarations) 
                                   (parseRightHandSide rhs)
            nodata (Left _) = error "Data declaration in where clause illegal."
            nodata (Right term) = term

-- | Parses a right hand side.
parseRightHandSide :: HsRhs -> Term
parseRightHandSide rhs = case rhs of
    HsUnGuardedRhs expr -> parseExpression expr
    
    -- Unsuported features.
    HsGuardedRhss _ -> error "Guards are not supported."

-- | Parses a pattern which solely contains a variable name.
parseNamePattern :: HsPat -> Name
parseNamePattern pattern = case pattern of
    HsPVar name -> parseName name
    
    -- Unsuported features.
    _ -> error "Pattern matching is only supported in case alternatives."

-- | Parses an operator. 
parseOperator :: HsQOp -> Term
parseOperator op = case op of
                    HsQVarOp n -> VariableTerm $ parseQName n
                    HsQConOp n -> VariableTerm $ parseQName n

-- | Parses a single case alternative.
parseCaseAlternative :: HsAlt -> (Pattern, Term)
parseCaseAlternative (HsAlt _ pat (HsUnGuardedAlt rhs) _) = (ppat pat, parseExpression rhs)
 where ppat pat = case pat of
                   HsPVar var      -> Variable $ parseName var
                   HsPApp con args -> Pattern (parseQName con) (map varpat args)
                   HsPParen p      -> ppat p
                   HsPLit _        -> error "Pattern matching on literals is not supported." -- TODO?
                   _               -> error "Only simple pattern matching is supported."
       varpat (HsPVar v) = parseName v
       varpat _          = error "Nested patterns are not supported." -- TODO?: this could be rewritten as a nested case.
parseCaseAlternative (HsAlt _ _ (HsGuardedAlts _) _) = error "Guards are not supported."  

-- | Parses a constructor declaration within a datatype definition.
parseDataCon :: HsConDecl -> DataCon
parseDataCon (HsRecDecl _ _ _) = error "Record syntax is not suppported."
parseDataCon (HsConDecl _ name args) = DataCon (parseName name) (map parseArg args)
 where parseArg (HsBangedTy   t) = parseType t
       parseArg (HsUnBangedTy t) = parseType t

-- | Parses a type, from within a data declaration.
parseType :: HsType -> Type
parseType ty = case ty of
                HsTyFun   a b -> Arrow Nothing (parseType a) (parseType b)
                HsTyTuple ts  -> TupleType $ map parseType ts
                HsTyApp (HsTyCon (Special HsListCon)) t   -> ListType $ parseType t
                HsTyApp _ _ -> error "Parameterized types other than lists and tuples are not supported."
                HsTyVar _   -> error "Unbound type variable."
                HsTyCon _   -> error "Unapplied type constructor.   "
