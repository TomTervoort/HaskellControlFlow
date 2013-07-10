module HaskellControlFlow.Analysis.CfaSolver where

import HaskellControlFlow.Calculus.Calculus (Name)
import HaskellControlFlow.Calculus.Types

import qualified Data.Map as M
import qualified Data.Set as S

-- | Annotation constraint.
data AnnConstraint = InclusionConstraint AnnVar Name
                   | SubstituteConstraint AnnVar AnnVar
                     deriving (Show)

-- | Annotation environment.
data AnnEnv = AnnEnv (M.Map AnnVar (S.Set Name)) (M.Map AnnVar AnnVar)

-- | Annotation constraints.
type AnnConstraints = [AnnConstraint]

-- | Constraint solver.
solveAnnConstraints :: AnnConstraints -> AnnEnv
solveAnnConstraints = foldr go (AnnEnv M.empty M.empty)
 where
  go x (AnnEnv allNames substitutions) = case x of
    InclusionConstraint var name ->
        let
            realVar = cannonicalVarName var substitutions
            
            varNames = M.findWithDefault S.empty realVar allNames
            newNames = M.insert realVar (S.insert name varNames) allNames

        in AnnEnv newNames substitutions
    
    SubstituteConstraint lhs rhs ->
        let compareAnn lhs_ rhs_
              = let realLhs_ = cannonicalVarName lhs_ substitutions
                    realRhs_ = cannonicalVarName rhs_ substitutions
                in case () of
                    _ | realLhs_ == realRhs_ -> EQ
                    _ | Just _ <- M.lookup realLhs_ allNames -> GT
                    _ -> LT

            insertSubstitution lhs_ rhs_
              = let realLhs_ = cannonicalVarName lhs_ substitutions
                    realRhs_ = cannonicalVarName rhs_ substitutions
                in case M.lookup lhs_ substitutions of
                        Just _ ->
                            -- Let's merge these two.
                            let
                                lhsNames    = M.findWithDefault S.empty realLhs_ allNames
                                rhsNames    = M.findWithDefault S.empty realRhs_ allNames
                                unionNames  = lhsNames `S.union` rhsNames
                                newAllNames = M.insert realLhs_ unionNames $ M.delete realRhs_ allNames
                                newSubstitutions = M.insert realRhs_ realLhs_ substitutions
                            in
                                AnnEnv newAllNames newSubstitutions
                        Nothing ->
                            -- Insert a new one.
                            AnnEnv allNames (M.insert lhs_ realRhs_ substitutions)

        in case compareAnn lhs rhs of
            EQ -> AnnEnv allNames substitutions
            LT -> insertSubstitution lhs rhs
            GT -> insertSubstitution rhs lhs

-- | Normalizes a variable name.
cannonicalVarName :: AnnVar -> M.Map AnnVar AnnVar -> AnnVar
cannonicalVarName var substitutions = case M.lookup var substitutions of
    Just substitution -> cannonicalVarName substitution substitutions
    Nothing           -> var

-- | Looks up annotation names in the solved annotations.
lookupAnnNames :: AnnVar -> AnnEnv -> [Name]
lookupAnnNames var (AnnEnv allNames substitutions) =
    case M.lookup (cannonicalVarName var substitutions) allNames of
        Just namesSet -> S.toList namesSet
        Nothing       -> []
