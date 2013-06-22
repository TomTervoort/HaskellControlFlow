{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Parser.Parser (parseHaskellFile) where

import HaskellControlFlow.Calculus.Calculus

import Language.Haskell.Parser
import Language.Haskell.Syntax

-- Parses a haskell file.
parseHaskellFile :: FilePath -> IO Term
parseHaskellFile filename = do
    -- Read file contents.
    contents <- readFile filename
    
    -- Parse module.
    return $ case parseModuleWithMode (ParseMode {parseFilename = filename}) contents of
        ParseOk hsModule -> parseHaskellModule hsModule
        ParseFailed (SrcLoc {srcLine = line, srcColumn = column}) message ->
            error $ filename ++ (':' : show line) ++ (':' : show column) ++ (':' : message)

-- Parses a module.
parseHaskellModule :: HsModule -> Term
parseHaskellModule (HsModule _ _ _ _ declarations) =
    LetInTerm {letTerms = concatMap parseDeclaration declarations
              ,inTerm   = VariableTerm {varName = "main"}}

-- Parses a declaration.
parseDeclaration :: HsDecl -> [NamedTerm]
parseDeclaration declaration = case declaration of
    HsTypeDecl _ _ _ _ -> [] -- TODO: Ignore? Can it rename data notation?
    HsTypeSig _ _ _    -> []
    
    HsDataDecl _ context name names constructorDeclarations moreNames -> error "Not implemented yet." -- TODO: Handle.
    
    HsPatBind _ pattern rhs whereDeclarations ->
        [NamedTerm {name = parsePattern pattern, term = parseLambda [] rhs whereDeclarations}]
    
    HsFunBind [HsMatch _ name patterns rhs whereDeclarations] ->
        [NamedTerm {name = parseName name, term = parseLambda patterns rhs whereDeclarations}]
    
    -- Unsuported features.
    HsFunBind _                 -> error "Pattern matching not supported."
    HsNewTypeDecl _ _ _ _ _ _   -> error "New type notation not supported."
    HsClassDecl _ _ _ _ _       -> error "Class notation not supported."
    HsInfixDecl _ _ _ _         -> error "Infix notation not supported."
    HsInstDecl _ _ _ _ _        -> error "Instance notation not supported."
    HsDefaultDecl _ _           -> error "Default notation not supported."
    HsForeignImport _ _ _ _ _ _ -> error "Foreign import not supported."
    HsForeignExport _ _ _ _ _   -> error "Foreign export not supported."

-- Parses an expression.
parseExpression :: HsExp -> Term
parseExpression expr = case expr of
    HsNegApp subExpr -> error "Not implemented yet." -- TODO: Implement.
    HsCase expr alternatives -> error "Not implemented yet." -- TODO: Implement.
    HsTuple values -> error "Not implemented yet." -- TODO: Implement.
    HsList values -> error "Not implemented yet." -- TODO: Implement.
    
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
        LetInTerm {letTerms = concatMap parseDeclaration letDeclarations
                   ,inTerm  = parseExpression inExpr}
    
    HsIf firstExpr thenExpr elseExpr ->
        IfTerm {exprTerm = parseExpression firstExpr
               ,thenTerm = parseExpression thenExpr
               ,elseTerm = parseExpression elseExpr}
    
    HsParen subExpr          -> parseExpression subExpr
    HsExpTypeSig _ subExpr _ -> parseExpression subExpr
    
    -- Unsuported features.
    HsInfixApp _ _ _       -> error "Infix notation not supported." -- TODO: Operators?
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
    
    HsAsPat _ _ -> error "Pattern matching not supported."
    HsWildCard  -> error "Pattern matching not supported."
    HsIrrPat _  -> error "Pattern matching not supported."

-- Parses a literal (constant) value.
parseLiteral :: HsLiteral -> Term
parseLiteral literal = case literal of
    HsChar char	    -> ConstantTerm {constant = CharConst char}
    HsString string	-> ConstantTerm {constant = StringConst string}
    HsInt integer   -> ConstantTerm {constant = IntegerConst integer}
    HsFrac rational	-> ConstantTerm {constant = DoubleConst rational}
    
    -- Unsuported features.
    _ -> error "Unboxed literals are not supported."

-- Parses a qualified name.
parseQName :: HsQName -> Name
parseQName qName = case qName of
    UnQual name -> parseName name
    
    -- Unsuported features.
    Qual _ _  -> error "Qualified names are not supported."
    Special _ -> error "Special constructors are not supported." -- TODO: Implement?

-- Parses a name.
parseName :: HsName -> Name
parseName fullName = case fullName of
    HsIdent name  -> name
    HsSymbol name -> name

-- Parses a lambda expression.
parseLambda :: [HsPat] -> HsRhs -> [HsDecl] -> Term
parseLambda patterns rhs whereDeclarations = 
    foldr (\arg term -> AbstractionTerm {argName = arg, bodyTerm = term}) bodyTerm arguments
        where
            arguments = map parsePattern patterns
            bodyTerm  = case whereDeclarations of
                [] -> parseRightHandSide rhs
                _  -> LetInTerm {letTerms = concatMap parseDeclaration whereDeclarations
                                ,inTerm   = parseRightHandSide rhs}

-- Parses a right hand side.
parseRightHandSide :: HsRhs -> Term
parseRightHandSide rhs = case rhs of
    HsUnGuardedRhs expr -> parseExpression expr
    
    -- Unsuported features.
    HsGuardedRhss _ -> error "Guards are not supported."

-- Parses a pattern.
parsePattern :: HsPat -> Name
parsePattern pattern = case pattern of
    HsPVar name -> parseName name
    
    -- Unsuported features.
    _ -> error "Pattern matching not supported."
