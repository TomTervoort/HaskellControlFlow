{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Parser.Parser (parseHaskellFile) where

import Language.Haskell.Parser
import Language.Haskell.Syntax

import System.IO

-- Parses a haskell file.
parseHaskellFile :: FilePath -> IO (ParseResult HsModule)
parseHaskellFile filename = do
    -- Read file contents.
    contents <- readFile filename
    
    -- Parse module.
    return $ parseModuleWithMode (ParseMode {parseFilename = filename}) contents
