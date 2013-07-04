{-# LANGUAGE Haskell2010 #-}

module Main(main) where

import HaskellControlFlow.Parser.Parser
import HaskellControlFlow.Calculus.Calculus
import HaskellControlFlow.Calculus.Formatter
import HaskellControlFlow.Calculus.Types
import HaskellControlFlow.Analysis.Inference

import System.Environment
import Data.List

-- | Walks over typed tree, and shows possible functions of applications.
showAnalysis :: AnnEnv -> Term Type -> IO ()
showAnalysis annEnv tt = case tt of
    ConstantTerm {} ->
        return ()
        
    VariableTerm {} ->
        return ()
        
    FixTerm {fixedTerm = fixedTerm} -> do
        showAnalysis annEnv fixedTerm
    
    ApplicationTerm {lhsTerm = lhsTerm, rhsTerm = rhsTerm} -> do
        showAnalysis annEnv lhsTerm
        showAnalysis annEnv rhsTerm
        
        putStr $ "Left hand side: " ++ formatTerm lhsTerm
        putStr $ "Right hand side: " ++ formatTerm rhsTerm
        
        putStrLn $ "Left hand side type: " ++ (show $ annotation lhsTerm)
        putStrLn $ "Right hand side type: " ++ (show $ annotation rhsTerm)
        
        case typeAnn $ annotation lhsTerm of
            Just var ->
                putStrLn $ "Possible named functions: " ++ (intercalate ", " $ lookupAnnNames var annEnv)
            Nothing ->
                putStrLn "Possible named functions: none"
        
        putStr "\n"
        
    AbstractionTerm {bodyTerm = bodyTerm} ->
        showAnalysis annEnv bodyTerm
        
    LetInTerm {letTerm = (NamedTerm {term = letTerm}), inTerm = inTerm} -> do
        showAnalysis annEnv letTerm
        showAnalysis annEnv inTerm
        
    CaseTerm {exprTerm = exprTerm, alts = alts} -> do
        showAnalysis annEnv exprTerm
        mapM_ (\(_, term) -> showAnalysis annEnv term) alts
        
    ListTerm {terms = terms} -> do
        mapM_ (showAnalysis annEnv) terms
        
    TupleTerm {terms = terms} -> do
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
    putStrLn $ formatTerm (topExpr program)
    
    -- Analyse it.
    let env = constructorTypes (datatypes program) initTyEnv
    (programType, tt, annEnv) <- inferPrincipalType (topExpr program) (datatypes program) env
    
    -- Show main type.
    putStrLn $ "Type of the 'main' function: " ++ show programType ++ "\n"
    
    -- Show analysis.
    putStrLn "Result of the control flow analysis:\n"
    showAnalysis annEnv tt
    
    return ()
