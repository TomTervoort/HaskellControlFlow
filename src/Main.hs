{-# LANGUAGE Haskell2010 #-}

module Main(main) where

import HaskellControlFlow.Parser.Parser
import HaskellControlFlow.Calculus.Formatter
import HaskellControlFlow.Calculus.Types
import HaskellControlFlow.Calculus.TypedCalculus
import HaskellControlFlow.Analysis.Inference

import System.Environment

-- | Walks over typed tree, and shows possible functions of applications.
showAnalysis :: TypedTerm -> IO ()
showAnalysis tt = case tt of
    TypedConstantTerm {} -> return ()
    TypedVariableTerm {} -> return ()
    TypedApplicationTerm {lhsTerm = lhsTerm, rhsTerm = rhsTerm} -> do
        showAnalysis lhsTerm
        showAnalysis rhsTerm
        
        putStrLn $ "Left hand side type: " ++ (show $ termType lhsTerm)
        putStrLn $ "Right hand side type: " ++ (show $ termType rhsTerm)
        
        case typeAnn $ termType lhsTerm of
            Just var -> putStrLn var
            Nothing  -> putStrLn "This should not happen: left hand side should be a function."
        
        putStrLn "\n"
        
    TypedAbstractionTerm {bodyTerm = bodyTerm} -> showAnalysis bodyTerm
    TypedLetInTerm {letTerm = (NamedTypedTerm {term = letTerm}), inTerm = inTerm} -> do
        showAnalysis letTerm
        showAnalysis inTerm
        
    TypedCaseTerm {exprTerm = exprTerm, alts = alts} -> do
        showAnalysis exprTerm
        mapM_ (\(p, term) -> showAnalysis term) alts
        
    TypedListTerm {terms = terms} -> do
        mapM_ showAnalysis terms
        
    TypedTupleTerm {terms = terms} -> do
        mapM_ showAnalysis terms

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
    putStr $ formatCalculus (topExpr program)
    
    -- Analyse it.
    let env = constructorTypes (datatypes program) initTyEnv
    (programType, tt, finalEnv, constraints) <- inferPrincipalType (topExpr program) (datatypes program) env
    
    -- Show analysis.
    showAnalysis tt
    
    
    
    putStrLn $ show programType
    putStrLn "\n"
    putStrLn $ show finalEnv
    putStrLn "\n"
    putStrLn $ show constraints
    putStrLn "\n"
    putStrLn $ show tt
    
    return ()
