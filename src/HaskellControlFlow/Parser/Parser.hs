{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Parser.Parser (parseHaskellFile) where

import HaskellControlFlow.Calculus.Calculus

import Language.Haskell.Parser
import Language.Haskell.Syntax

-- Parses a haskell file.
parseHaskellFile :: FilePath -> IO [HsDecl]
parseHaskellFile filename = do
    -- Read file contents.
    contents <- readFile filename
    
    -- Parse module.
    return $ case parseModuleWithMode (ParseMode {parseFilename = filename}) contents of
        ParseOk hsModule -> parseHaskellModule hsModule
        ParseFailed (SrcLoc {srcLine = line, srcColumn = column}) message ->
            error $ filename ++ (':' : show line) ++ (':' : show column) ++ (':' : message)

-- Parses a module.
parseHaskellModule :: HsModule -> [HsDecl]
parseHaskellModule (HsModule _ _ _ _ declarations) = map parseDeclaration declarations

-- Parses a declaration.
parseDeclaration :: HsDecl -> HsDecl
parseDeclaration declaration = declaration
