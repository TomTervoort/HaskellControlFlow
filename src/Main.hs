{-# LANGUAGE Haskell2010 #-}

module Main(main) where

import HaskellControlFlow.Parser.Parser
import HaskellControlFlow.Calculus.Calculus
import HaskellControlFlow.Calculus.Formatter
import HaskellControlFlow.Calculus.Types
import HaskellControlFlow.Analysis.CfaSolver
import HaskellControlFlow.Analysis.Inference

import System.Environment
import Data.List
import Data.Fresh
import Data.Traversable (traverse)

-- | Walks over typed tree, and shows possible functions of applications.
showAnalysis :: AnnEnv -> Term Type -> IO ()
showAnalysis annEnv tt = case tt of
    LiteralTerm _ _ ->
        return ()
        
    VariableTerm _ _ _ ->
        return ()

    HardwiredTerm _ _ ->
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

        putStr "Possible named functions: "
        let annNames
                = maybe [] (\var -> lookupAnnNames var annEnv)
                . typeAnn . annotation $ lhsTerm
        if null annNames
            then putStrLn "(none)"
            else putStrLn . intercalate ", " . map show $ annNames
        
        putStrLn ""
        
    AbstractionTerm _ _ bodyTerm ->
        showAnalysis annEnv bodyTerm
        
    LetInTerm _ _ letTerm inTerm -> do
        showAnalysis annEnv letTerm
        showAnalysis annEnv inTerm
        
    CaseTerm _ exprTerm alts -> do
        showAnalysis annEnv exprTerm

        let dataAnn = case annotation exprTerm of
                DataType psi _   -> Just psi
                ListType psi _   -> Just psi
                TupleType psi _  -> Just psi
                _ -> Nothing

        case dataAnn of
            Nothing -> return ()
            Just psi -> do
                putStr $ "Scrutinee: " ++ formatTerm exprTerm
                putStrLn $ "Scrutinee type: " ++ (show $ annotation exprTerm)
                case psi of
                    Just var -> do
                        putStr "Possible creation sites: "                        
                        let ns = lookupAnnNames var annEnv
                        putStrLn $ if null ns then "(none)" else intercalate "," (map show ns)
                    Nothing ->
                        putStrLn "(Failed to find creation site.)"
                putStrLn ""

        mapM_ (\(_, term) -> showAnalysis annEnv term) alts

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
    (programType, tt, annEnv) <- fmap fst . (\m -> runFreshT m (0::Integer)) $ do
        let top = topExpr program
        let top' = adornWithNames top
        top'' <- traverse (\(nm, _) -> fmap (\s -> (nm, TyVar ('$':show s))) fresh) top'
        inferPrincipalType top'' (dataTypes program)
    
    -- Show main type.
    putStrLn $ "Type of the 'main' function: " ++ show programType ++ "\n"
    
    -- Show analysis.
    putStrLn "Result of the control flow analysis:\n"
    showAnalysis annEnv tt
    
    return ()
