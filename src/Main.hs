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
    LiteralTerm _ _ ->
        return ()
        
    VariableTerm _ _ ->
        return ()
        
    FixTerm _ fixedTerm -> do
        showAnalysis annEnv fixedTerm
    
    ApplicationTerm _ lhsTerm rhsTerm -> do
        showAnalysis annEnv lhsTerm
        showAnalysis annEnv rhsTerm
        
        putStr $ "Left hand side: " ++ formatTerm lhsTerm
        putStr $ "Right hand side: " ++ formatTerm rhsTerm
        
        putStrLn $ "Left hand side type: " ++ (show $ annotation lhsTerm)
        putStrLn $ "Right hand side type: " ++ (show $ annotation rhsTerm)

        let annNames
                = maybe [] (\var -> lookupAnnNames var annEnv)
                . typeAnn . annotation $ lhsTerm
        if null annNames
            then putStrLn "Possible named functions: none"
            else putStrLn $ "Possible named functions: " ++ (intercalate ", " annNames)
        
        putStr "\n"
        
    AbstractionTerm _ _ bodyTerm ->
        showAnalysis annEnv bodyTerm
        
    LetInTerm _ _ letTerm inTerm -> do
        showAnalysis annEnv letTerm
        showAnalysis annEnv inTerm
        
    CaseTerm _ exprTerm alts -> do
        showAnalysis annEnv exprTerm
        mapM_ (\(_, term) -> showAnalysis annEnv term) alts
        
    ListTerm _ terms -> do
        mapM_ (showAnalysis annEnv) terms
        
    TupleTerm _ terms -> do
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
    (programType, tt, annEnv) <- inferPrincipalType (topExpr program) (dataTypes program)
    
    -- Show main type.
    putStrLn $ "Type of the 'main' function: " ++ show programType ++ "\n"
    
    -- Show analysis.
    putStrLn "Result of the control flow analysis:\n"
    showAnalysis annEnv tt
    
    return ()
