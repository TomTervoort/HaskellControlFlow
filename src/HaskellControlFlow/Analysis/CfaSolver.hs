module HaskellControlFlow.Analysis.CfaSolver where

import HaskellControlFlow.Calculus.Calculus (NameAdornment)
import HaskellControlFlow.Calculus.Types

import Control.Arrow

import qualified Data.Partition as P
import qualified Data.Map as M
import qualified Data.Set as S

-- | Annotation constraint.
data AnnConstraint = InclusionConstraint AnnVar NameAdornment
                   | SubstituteConstraint AnnVar AnnVar

-- | Annotation environment.
data AnnEnv = AnnEnv (P.Partition AnnVar) (M.Map AnnVar (S.Set NameAdornment))

-- | Annotation constraints.
type AnnConstraints = [AnnConstraint]

partAnnConstraints :: [AnnConstraint] -> ([(AnnVar, NameAdornment)], [(AnnVar, AnnVar)])
partAnnConstraints = foldr go ([], [])
  where
    go (InclusionConstraint var name) (ics, scs) = ((var, name):ics, scs)
    go (SubstituteConstraint lhs rhs) (ics, scs) = (ics, (lhs, rhs):scs)

buildPartition :: (Ord a) => [(a, a)] -> P.Partition a
buildPartition = foldr (\(l, r) p -> P.join l r p) P.discrete

-- | Constraint solver.
solveAnnConstraints :: AnnConstraints -> AnnEnv
solveAnnConstraints
    = (\(ics, p) -> makeEnv p ics)
    . second buildPartition
    . partAnnConstraints
    where
        makeEnv :: P.Partition AnnVar -> [(AnnVar, NameAdornment)] -> AnnEnv
        makeEnv p
            = AnnEnv p
            . M.fromListWith S.union
            . map (P.rep p *** S.singleton)

-- | Looks up annotation names in the solved annotations.
lookupAnnNames :: AnnVar -> AnnEnv -> [NameAdornment]
lookupAnnNames var (AnnEnv substitutions allNames)
    = maybe [] S.toList
    . M.lookup (P.rep substitutions var)
    $ allNames
