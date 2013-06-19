{-# LANGUAGE Haskell2010 #-}

module Main(main) where

import HaskellControlFlow.Parser.Parser

import System.Environment (getArgs)

-- Main method.
main :: IO ()
main =  do
    -- Fetch filename from arguments.
    args <- getArgs
    
    let filename = if length args == 1
        then head args
        else error "First argument must be a haskell filename."
    
    -- Parse it.
    calculus <- parseHaskellFile filename
    
    -- Show it.
    print calculus
    
    return ()
