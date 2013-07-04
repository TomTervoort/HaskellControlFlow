{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Parser.Parser (parseHaskellFile) where

import HaskellControlFlow.Calculus.Calculus
import HaskellControlFlow.Calculus.Types

import Language.Haskell.Parser
import Language.Haskell.Syntax

import Data.Either
import Data.Maybe

-- | Parses a haskell file.
parseHaskellFile :: FilePath -> IO (HaskellProgram ())
parseHaskellFile filename = do
    -- Read file contents.
    contents <- readFile filename
    
    -- Parse module.
    return $ case parseModuleWithMode (ParseMode {parseFilename = filename}) contents of
        ParseOk hsModule -> parseHaskellModule hsModule
        ParseFailed (SrcLoc {srcLine = line, srcColumn = column}) message ->
            error $ filename ++ (':' : show line) ++ (':' : show column) ++ (':' : message)

-- | Parses a module.
parseHaskellModule :: HsModule -> HaskellProgram ()
parseHaskellModule (HsModule _ _ _ _ declarations) =
    let (defs, lets) = partitionEithers $ concatMap parseDeclaration declarations
     in HaskellProgram {dataTypes = foldr addDataDef initEnv defs,
                        topExpr   = letGroup lets (VariableTerm {varName = "main"})}

-- | Parses a data or function declaration.
parseDeclaration :: HsDecl -> [Either DataDef (NamedTerm ())]
parseDeclaration declaration = case declaration of
    HsTypeDecl _ _ _ _  -> [] -- Just skip them.
    HsInfixDecl _ _ _ _ -> [] -- Parser will take care of this.
    HsTypeSig _ _ _     -> [] -- We ignore type signatures and infer everything ourselves.
    
    HsDataDecl _ _ name params constructors _
     | not $ null params -> error "Parametrized data type declarations are not supported."
     | otherwise         -> [Left $ DataDef {dataName = parseName name, ctors = map parseDataCon constructors}]
    
    HsPatBind _ pattern rhs whereDeclarations ->
        [Right $ NamedTerm {name = parseNamePattern pattern, term = parseLambda [] rhs whereDeclarations}]
    
    HsFunBind matches -> 
     [Right $ uncurry NamedTerm (parseFunBindings matches)]

    -- Unsuported features.
    HsNewTypeDecl _ _ _ _ _ _   -> error "New type notation not supported."
    HsClassDecl _ _ _ _ _       -> error "Class notation not supported."
    HsInstDecl _ _ _ _ _        -> error "Instance notation not supported."
    HsDefaultDecl _ _           -> error "Default notation not supported."
    HsForeignImport _ _ _ _ _ _ -> error "Foreign import not supported."
    HsForeignExport _ _ _ _ _   -> error "Foreign export not supported."

-- | Parses an expression.
parseExpression :: HsExp -> Term ()
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
        letGroup (concatMap (rights . parseDeclaration) letDeclarations) 
                     (parseExpression inExpr)
    
    HsIf firstExpr thenExpr elseExpr ->
        CaseTerm {exprTerm = parseExpression firstExpr,
                  alts     = [
                              (Pattern "True" [],  parseExpression thenExpr),
                              (Pattern "False" [], parseExpression elseExpr)
                             ]}
    
    HsParen subExpr          -> parseExpression subExpr
    HsExpTypeSig _ subExpr _ -> parseExpression subExpr
    
    HsInfixApp l op r -> 
        ApplicationTerm {lhsTerm = ApplicationTerm () (parseOperator op) (parseExpression l)
                        ,rhsTerm = parseExpression r}

    HsLeftSection exp op  -> ApplicationTerm () (parseOperator op) (parseExpression exp)
    
    HsNegApp subExpr -> 
        ApplicationTerm () (VariableTerm () "negate") $ parseExpression subExpr

    HsCase expr alternatives -> 
     CaseTerm {exprTerm = parseExpression expr,
               alts     = map parseCaseAlternative alternatives}

    HsTuple values -> 
     TupleTerm () $ map parseExpression values
    HsList values -> 
     ListTerm () $ map parseExpression values

    -- Unsuported features.
    HsDo _                 -> error "Do notation not supported."
    HsRecConstr _ _	       -> error "Record notation not supported."
    HsRecUpdate _ _        -> error "Record notation not supported."
    HsEnumFrom _           -> error "Enum notation not supported."
    HsEnumFromTo _ _       -> error "Enum notation not supported."	
    HsEnumFromThen _ _	   -> error "Enum notation not supported."
    HsEnumFromThenTo _ _ _ -> error "Enum notation not supported."
    HsListComp _ _	       -> error "List comprehensions not supported."
    HsRightSection _ _     -> error "Right section not supported."
    
    HsAsPat _ _ -> error "Pattern matching only supported on the first argument or within case alternatives."
    HsWildCard  -> error "Pattern matching only supported on the first argument or within case alternatives."
    HsIrrPat _  -> error "Pattern matching only supported on the first argument or within case alternatives."

-- | Parses a literal (constant) value.
parseLiteral :: HsLiteral -> Term ()
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

-- | Parses a set of bindings to the same function. Unless there is only a single match with a 
--   variable, the resulting term will be a case expression.
parseFunBindings :: [HsMatch] -> (Name, Term ())
parseFunBindings ms = 
 case map parseFuncBinding ms of
  []          -> error "Empty list passed to parseFunBindings."
  [(n, Just (Variable v), t)] -> (n, AbstractionTerm () v t)
  [(n, Nothing, t)]           -> (n, t)
  xs                          -> (getName xs, AbstractionTerm () fresh 
                                                $ CaseTerm () (VariableTerm () fresh) (map getAlt xs))
 
 where fresh = "@" -- Not really a fresh variable. But since @ is an illegal Haskell identifier
                   -- it can not shadow user code.
       getName ((n, _, _):xs) | all (\(n',_,_) -> n == n') xs = n
       getName _ = error "Inconsistant function names within same binding."
       getAlt (_, Just p, rhs) = (p, rhs)
       getAlt (_, Nothing, _)  = error "Different number of arguments in function bindings."

-- | Parses a function binding. Unless it has no arguments (in which case the second result is 
--   Nothing) the first argument will be parsed as a pattern (but may still be a variable) while 
--   any others are required to be variables and are rewritten to abstractions within the Term.
parseFuncBinding :: HsMatch -> (Name, Maybe Pattern, Term ())
parseFuncBinding (HsMatch _ name args rhs whereDecls) =
 case args of
  []     -> (parseName name, Nothing, parseLambda args rhs whereDecls)
  (a:as) -> (parseName name, Just $ parsePattern a, parseLambda as rhs whereDecls)

-- | Parses a lambda expression.
parseLambda :: [HsPat] -> HsRhs -> [HsDecl] -> Term ()
parseLambda patterns rhs whereDeclarations = 
    foldr (\arg term -> AbstractionTerm {argName = arg, bodyTerm = term}) bodyTerm arguments
        where
            arguments = map parseNamePattern patterns
            bodyTerm  = case whereDeclarations of
                [] -> parseRightHandSide rhs
                _  -> letGroup (concatMap (map nodata . parseDeclaration) whereDeclarations) 
                                   (parseRightHandSide rhs)
            nodata (Left _) = error "Data declaration in where clause illegal."
            nodata (Right term) = term

-- | Parses a right hand side.
parseRightHandSide :: HsRhs -> Term ()
parseRightHandSide rhs = case rhs of
    HsUnGuardedRhs expr -> parseExpression expr
    
    -- Unsuported features.
    HsGuardedRhss _ -> error "Guards are not supported."

-- | Parses a pattern which solely contains a variable name.
parseNamePattern :: HsPat -> Name
parseNamePattern pattern = case pattern of
    HsPVar name -> parseName name
    HsPWildCard -> error "Wildcards are not supported."

    -- Unsuported features.
    _ -> error "Pattern matching is only supported on the first argument or within case alternatives."

-- | Parses an operator. 
parseOperator :: HsQOp -> Term ()
parseOperator op = case op of
                    HsQVarOp n -> VariableTerm () $ parseQName n
                    HsQConOp n -> VariableTerm () $ parseQName n

-- | Parses a single case alternative.
parseCaseAlternative :: HsAlt -> (Pattern, Term ())
parseCaseAlternative (HsAlt _ pat (HsUnGuardedAlt rhs) _) = (parsePattern pat, parseExpression rhs)
parseCaseAlternative (HsAlt _ _   (HsGuardedAlts _)    _) = error "Guards are not supported."  

-- | Parses a pattern.
parsePattern :: HsPat -> Pattern
parsePattern pat = case pat of
                    HsPVar var      -> Variable $ parseName var
                    HsPApp con args -> Pattern (parseQName con) (map varpat args)
                    HsPParen p      -> parsePattern p
                    HsPLit _        -> error "Pattern matching on literals is not supported." -- TODO?
                    _               -> error "Only simple pattern matching is supported."
 where varpat (HsPVar v) = parseName v
       varpat _          = error "Nested patterns are not supported."

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
                HsTyCon name -> typeFromName $ parseQName name
                HsTyApp _ _ -> error "Parameterized types other than lists and tuples are not supported."
                HsTyVar _   -> error "Unbound type variable."

