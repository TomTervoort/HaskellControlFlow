{-# LANGUAGE Haskell2010 #-}

module Main(main) where

import HaskellControlFlow.Parser.Parser
import HaskellControlFlow.Calculus.Formatter
import HaskellControlFlow.Calculus.Types
import HaskellControlFlow.Analysis.Inference

import System.Environment

-- Main method.
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
    
    let env = constructorTypes (datatypes program) initTyEnv
    (programType, finalEnv, tt, constraints) <- inferPrincipalType (topExpr program) (datatypes program) env
    
    putStrLn $ show programType
    
    putStrLn $ show finalEnv
    
    putStrLn $ show constraints
    
    putStrLn $ show tt
    
    return ()
