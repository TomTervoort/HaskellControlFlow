{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Calculus where

import Data.Graph
import Data.List
import Data.Maybe

-- | Graph of mutual calls within a group of let's. The outgoing edge list may contain names that 
--   are not present in the graph. These should be ignored.
type CallGraph = [(Term, Name, [Name])]

-- | Extended lambda calculus.
type Calculus = Term

-- | Terms.
data Term = ConstantTerm {constant :: Constant}
          | VariableTerm {varName :: Name}
          | ApplicationTerm {lhsTerm :: Term, rhsTerm :: Term}
          | AbstractionTerm {argName :: Name, bodyTerm :: Term}
          | LetInTerm {letTerm :: NamedTerm, inTerm :: Term}
          | CaseTerm {exprTerm :: Term, alts :: [(Pattern, Term)]}          
          | ListTerm {terms :: [Term]}
          | TupleTerm {terms :: [Term]}
          | FixTerm {fixedTerm :: Term}
            deriving (Show)

-- | Patterns within case-expressions.
data Pattern = Variable Name
             | Pattern {ctorName :: Name, ctorArgs :: [Name]}
                deriving (Show)

-- | Named term.
data NamedTerm = NamedTerm {name :: Name, term :: Term}
                 deriving (Show)

-- | Constants.
data Constant = IntegerConst Integer
              | DoubleConst Rational
              | StringConst String
              | CharConst Char
                deriving (Show)

-- | Abstraction name.
type Name = String

-- | `replaceVar a b t` replaces each occurence of a variable named `a` within `t` with `b`.
replaceVar :: Name -> Term -> Term -> Term
replaceVar from to = rep
 where rep t = 
        case t of
         ConstantTerm c                          -> ConstantTerm c
         VariableTerm v              | v == from -> to
                                     | otherwise -> VariableTerm v
         ApplicationTerm l r                     -> ApplicationTerm (rep l) (rep r)
         AbstractionTerm n b         | n == from -> AbstractionTerm n b -- Name is shadowed.
                                     | otherwise -> AbstractionTerm n (rep b)
         LetInTerm (NamedTerm n a) b | n == from -> LetInTerm (NamedTerm n a) b
                                     | otherwise -> LetInTerm (NamedTerm n $ rep a) (rep b)
         CaseTerm e as                           -> CaseTerm (rep e) $ map repAlt as
         ListTerm ts                             -> ListTerm (map rep ts)
         TupleTerm ts                            -> TupleTerm (map rep ts)
         FixTerm f                               -> FixTerm (rep f)
       
       repAlt p@(Variable n, t)   | n == from = p
                                  | otherwise = (Variable n, rep t)
       repAlt p@(Pattern c as, t) | from `elem` as = p
                                  | otherwise = (Pattern c as, rep t) 

makeCallGraph :: [NamedTerm] -> CallGraph
makeCallGraph = map (\(NamedTerm n t) -> (t, n, names t))
 where names t = 
        case t of
         VariableTerm n -> [n]
         ApplicationTerm l r -> names l ++ names r
         AbstractionTerm n b -> removeAll n $ names b -- Do not include the scoped variable.
         LetInTerm (NamedTerm n t1) t2 -> removeAll n $ names t1 ++ names t2
         CaseTerm e as -> names e ++ concatMap altNames as
         ListTerm ts -> concatMap names ts
         TupleTerm ts -> concatMap names ts
         FixTerm f -> names f
       
       removeAll x ys = ys \\ repeat x
       altNames (Variable n  , t) = removeAll n $ names t
       altNames (Pattern _ as, t) = foldr (\a -> (removeAll a .)) id as $ names t

-- | Identifies the strongly connected components within the graph, adds non-recursive versions for
--   the nodes in these components and then redefines these nodes with a fixed-point combinator.
--   Returns a list of named terms in such an order that no term variables will refer to a let that
--   is positioned further in the list.
fixRecursion :: CallGraph -> [NamedTerm]
fixRecursion = concatMap handleSCC . stronglyConnCompR
 where handleSCC (AcyclicSCC (t, n, _)) = [NamedTerm n t]
       handleSCC (CyclicSCC ns) = uncurry (++) $ unzip $ map (handleNode $ map middle ns) ns
       middle (_,x,_) = x
       absName n = "@" ++ n ++ "@"

       handleNode :: [Name] -> (Term, Name, [Name]) -> (NamedTerm, NamedTerm)
       handleNode group (t, name, _) = (NamedTerm (absName name) $ abstracted group, 
                                        NamedTerm name           $ fixed nameIndex)
        where nameIndex = fromJust $ findIndex (== name) group
              
              abstracted :: [Name] -> Term
              abstracted []     = t
              abstracted (n:ns) = let freshName = n ++ "@" ++ name
                                     in AbstractionTerm freshName 
                                          $ replaceVar n (VariableTerm freshName)
                                          $ abstracted ns

              fixName i = "@F" ++ show i ++ "@" ++ name
              groupSize = length group

              fixed :: Int -> Term
              fixed i = FixTerm $ AbstractionTerm (fixName i) 
                                $ appSequence 
                                $ [VariableTerm $ absName $ group !! i] 
                                    ++ map VariableTerm (take (i - 1) group)
                                    ++ [VariableTerm $ fixName i]
                                    ++ map fixed [i .. groupSize - 1]

              appSequence :: [Term] -> Term
              appSequence = foldl1 ApplicationTerm


namedTermsToLets :: [NamedTerm] -> Term -> Term
namedTermsToLets = foldr (\n -> (LetInTerm n .)) id


-- | Smart constructor for multiple let-terms following each other in an expression.
--   The lets may refer to each other, because this function will handle ordening and (mutual) 
--   recursion.
letGroup :: [NamedTerm] -> Term -> Term
letGroup lhss = namedTermsToLets $ fixRecursion $ makeCallGraph lhss



{-- letGroup [NamedTerm n def] t = LetInTerm (NamedTerm n def) t
letGroup (n:ns) t = LetInTerm n $ letGroup ns t
letGroup [] _ = error "Provide at least one named term." --}