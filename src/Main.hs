{-# LANGUAGE Haskell2010 #-}

module Main(main) where

import HaskellControlFlow.Parser.Parser
import HaskellControlFlow.Calculus.Formatter
import HaskellControlFlow.Calculus.Types
import HaskellControlFlow.Calculus.TypedCalculus
import HaskellControlFlow.Analysis.Inference

import System.Environment
import Data.List

-- | Walks over typed tree, and shows possible functions of applications.
showAnalysis :: AnnEnv -> TypedTerm -> IO ()
showAnalysis annEnv tt = case tt of
    TypedConstantTerm {} ->
        return ()
        
    TypedVariableTerm {} ->
        return ()
        
    TypedFixTerm {fixedTerm = fixedTerm} -> do
        showAnalysis annEnv fixedTerm
    
    TypedApplicationTerm {lhsTerm = lhsTerm, rhsTerm = rhsTerm} -> do
        showAnalysis annEnv lhsTerm
        showAnalysis annEnv rhsTerm
        
        putStrLn $ "Left hand side type: " ++ (show $ termType lhsTerm)  -- TODO: This still has unresolved vars!
        putStrLn $ "Right hand side type: " ++ (show $ termType rhsTerm) -- TODO: This still has unresolved vars!
        
        case typeAnn $ termType lhsTerm of
            Just var ->
                putStrLn $ "Possible named functions: " ++ (intercalate ", " $ lookupAnnNames var annEnv)
            Nothing ->
                putStrLn "Possible named functions: none"
        
        putStr "\n"
        
    TypedAbstractionTerm {bodyTerm = bodyTerm} ->
        showAnalysis annEnv bodyTerm
        
    TypedLetInTerm {letTerm = (NamedTypedTerm {term = letTerm}), inTerm = inTerm} -> do
        showAnalysis annEnv letTerm
        showAnalysis annEnv inTerm
        
    TypedCaseTerm {exprTerm = exprTerm, alts = alts} -> do
        showAnalysis annEnv exprTerm
        mapM_ (\(_, term) -> showAnalysis annEnv term) alts
        
    TypedListTerm {terms = terms} -> do
        mapM_ (showAnalysis annEnv) terms
        
    TypedTupleTerm {terms = terms} -> do
        mapM_ (showAnalysis annEnv) terms

-- | Main method.
main :: IO ()
main = do
    -- Fetch filename from arguments.
    args <- getArgs
    
    let filename = if length args == 1
        then head args
        else error "First argument must be a haskell filename."
    
    -- Parse it.
    program <- parseHaskellFile filename
    
    -- Show it.
    putStrLn "Extended calculus of program:"
    putStrLn $ formatCalculus (topExpr program)
    
    -- Analyse it.
    let env = constructorTypes (datatypes program) initTyEnv
    (programType, tt, _, annEnv) <- inferPrincipalType (topExpr program) (datatypes program) env
    
    -- Show main type.
    putStrLn $ "Type of the 'main' function: " ++ show programType ++ "\n"
    
    -- Show analysis.
    putStrLn "Result of the control flow analysis:\n"
    showAnalysis annEnv tt
    
    -- putStrLn "\n"
    -- putStrLn $ show finalEnv
    -- putStrLn "\n"
    -- putStrLn $ show annEnv
    -- putStrLn "\n"
    -- putStrLn $ show tt
    
    return ()
