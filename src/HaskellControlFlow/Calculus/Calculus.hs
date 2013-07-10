{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Calculus where

import Data.Graph
import Data.List
import Data.Maybe

import Debug.Trace

-- | Graph of mutual calls within a group of let's. The outgoing edge list may contain names that 
--   are not present in the graph. These should be ignored.
type CallGraph = [(Term (), Name, [Name])]

-- | Terms.
data Term a = LiteralTerm {annotation :: a, constant :: Literal}
            | VariableTerm {annotation :: a, varName :: Name}
            | ApplicationTerm {annotation :: a, lhsTerm :: Term a, rhsTerm :: Term a}
            | AbstractionTerm {annotation :: a, argName :: Name, bodyTerm :: Term a}
            | LetInTerm {annotation :: a, letTerm :: NamedTerm a, inTerm :: Term a}
            | CaseTerm {annotation :: a, exprTerm :: Term a, alts :: [(Pattern, Term a)]}
            | ListTerm {annotation :: a, terms :: [Term a]}
            | TupleTerm {annotation :: a, terms :: [Term a]}
            | FixTerm {annotation :: a, fixedTerm :: Term a}
              deriving (Show)

-- | Patterns within case-expressions.
data Pattern = Variable Name
             | Pattern {ctorName :: Name, ctorArgs :: [Name]}
               deriving (Show)

-- | Named term.
data NamedTerm a = NamedTerm {name :: Name, term :: Term a}
                   deriving (Show)

-- | Constants.
data Literal = IntegerLit Integer
             | RationalLit Rational
             | StringLit String
             | CharLit Char

instance Show Literal where
    show (IntegerLit x) = show x
    show (RationalLit x) = show (fromRational x :: Double)
    show (StringLit x) = show x
    show (CharLit x) = show x

-- | Abstraction name.
type Name = String

-- | Replaces the annotations on a term.
replaceAnnotation :: (a -> b) -> Term a -> Term b
replaceAnnotation f t = case t of
    LiteralTerm {annotation = ann} ->
        LiteralTerm {annotation = f ann
                     ,constant   = constant t}
    
    VariableTerm {annotation = ann} ->
        VariableTerm {annotation = f ann
                     ,varName    = varName t}
    
    ApplicationTerm {annotation = ann, lhsTerm = lhsTerm, rhsTerm = rhsTerm} ->
        ApplicationTerm {annotation = f ann
                        ,lhsTerm    = replaceAnnotation f lhsTerm
                        ,rhsTerm    = replaceAnnotation f rhsTerm}
    
    AbstractionTerm {annotation = ann, bodyTerm = bodyTerm} ->
        AbstractionTerm {annotation = f ann
                        ,argName    = argName t
                        ,bodyTerm   = replaceAnnotation f bodyTerm}
    
    LetInTerm {annotation = ann, letTerm = letTerm, inTerm = inTerm} ->
        LetInTerm {annotation = f ann
                  ,letTerm    = NamedTerm {name = name letTerm, term = replaceAnnotation f $ term letTerm}
                  ,inTerm     = replaceAnnotation f inTerm}
     
    CaseTerm {annotation = ann, exprTerm = exprTerm, alts = alts} ->
        CaseTerm {annotation = f ann
                 ,exprTerm   = replaceAnnotation f exprTerm
                 ,alts       = map (\(p, term) -> (p, replaceAnnotation f term)) alts}
    
    ListTerm {annotation = ann, terms = terms} ->
        ListTerm {annotation = f ann
                 ,terms      = map (replaceAnnotation f) terms}
    
    TupleTerm {annotation = ann, terms = terms} ->
        TupleTerm {annotation = f ann
                  ,terms      = map (replaceAnnotation f) terms}
    
    FixTerm {annotation = ann, fixedTerm = fixedTerm} ->
        FixTerm {annotation = f ann
                ,fixedTerm  = replaceAnnotation f fixedTerm}

-- | `replaceVar a b t` replaces each occurence of a variable named `a` within `t` with `b`.
replaceVar :: Name -> Term a -> Term a -> Term a
replaceVar from to = rep
 where rep t = 
        case t of
         LiteralTerm ann c                           -> LiteralTerm ann c
         VariableTerm ann v              | v == from -> to
                                         | otherwise -> VariableTerm ann v
         ApplicationTerm ann l r                     -> ApplicationTerm ann (rep l) (rep r)
         AbstractionTerm ann n b         | n == from -> AbstractionTerm ann n b -- Name is shadowed.
                                         | otherwise -> AbstractionTerm ann n (rep b)
         LetInTerm ann (NamedTerm n a) b | n == from -> LetInTerm ann (NamedTerm n a) b
                                         | otherwise -> LetInTerm ann (NamedTerm n $ rep a) (rep b)
         CaseTerm ann e as                           -> CaseTerm ann (rep e) $ map repAlt as
         ListTerm ann ts                             -> ListTerm ann (map rep ts)
         TupleTerm ann ts                            -> TupleTerm ann (map rep ts)
         FixTerm ann f                               -> FixTerm ann (rep f)
       
       repAlt p@(Variable n, t)   | n == from = p
                                  | otherwise = (Variable n, rep t)
       repAlt p@(Pattern c as, t) | from `elem` as = p
                                  | otherwise = (Pattern c as, rep t) 

makeCallGraph :: [NamedTerm ()] -> CallGraph
makeCallGraph = map (\(NamedTerm n t) -> (t, n, names t))
 where names t = 
        case t of
         LiteralTerm _ _ -> []
         VariableTerm _ n -> [n]
         ApplicationTerm _ l r -> names l ++ names r
         AbstractionTerm _ n b -> removeAll n $ names b -- Do not include the scoped variable.
         LetInTerm _ (NamedTerm n t1) t2 -> removeAll n $ names t1 ++ names t2
         CaseTerm _ e as -> names e ++ concatMap altNames as
         ListTerm _ ts -> concatMap names ts
         TupleTerm _ ts -> concatMap names ts
         FixTerm _ f -> names f
       
       removeAll _ [] = []
       removeAll x (y:ys) | x == y    = removeAll x ys
                          | otherwise = y : removeAll x ys
       
       altNames (Variable n  , t) = removeAll n $ names t
       altNames (Pattern _ as, t) = foldr (\a -> (removeAll a .)) id as $ names t

-- | Identifies the strongly connected components within the graph, adds non-recursive versions for
--   the nodes in these components and then redefines these nodes with a fixed-point combinator.
--   Returns a list of named terms in such an order that no term variables will refer to a let that
--   is positioned further in the list.
fixRecursion :: CallGraph -> [NamedTerm ()]
fixRecursion = concatMap handleSCC . stronglyConnCompR
 where handleSCC (AcyclicSCC (t, n, _)) = [NamedTerm n t]
       handleSCC (CyclicSCC ns) = uncurry (++) $ unzip $ map (handleNode $ map middle ns) ns
       middle (_,x,_) = x
       absName n = "@" ++ n ++ "@"

       handleNode :: [Name] -> (Term (), Name, [Name]) -> (NamedTerm (), NamedTerm ())
       handleNode group (t, name, _) = (NamedTerm (absName name) $ abstracted group, 
                                        NamedTerm name           $ fixed 0 nameIndex)
        where nameIndex = fromJust $ findIndex (== name) group
              
              abstracted :: [Name] -> Term ()
              abstracted []     = t
              abstracted (n:ns) = let freshName = n ++ "@" ++ name
                                     in AbstractionTerm () freshName 
                                          $ replaceVar n (VariableTerm () freshName)
                                          $ abstracted ns

              fixName i = "@F" ++ show i ++ "@" ++ name
              groupSize = length group

              fixed :: Int -> Int -> Term ()
              fixed defCount i = FixTerm () $ AbstractionTerm () (fixName i) 
                                            $ appSequence 
                                            $ [VariableTerm () $ absName $ group !! i] 
                                                ++ map (VariableTerm ()) (take defCount group)
                                                ++ map (fixed defCount) [defCount .. i - 1]
                                                ++ [VariableTerm () $ fixName i]
                                                ++ map (repName i . fixed (defCount + 1)) [i + 1 .. groupSize - 1]
              repName i = replaceVar (group !! i) (VariableTerm () $ fixName i)

              appSequence :: [Term ()] -> Term ()
              appSequence = foldl1 (ApplicationTerm ())

namedTermsToLets :: [NamedTerm ()] -> Term () -> Term ()
namedTermsToLets = foldr (\n -> (LetInTerm () n .)) id

-- | Smart constructor for multiple let-terms following each other in an expression.
--   The lets may refer to each other, because this function will handle ordening and (mutual) 
--   recursion.
letGroup :: [NamedTerm ()] -> Term () -> Term ()
letGroup lhss = namedTermsToLets $ fixRecursion $ makeCallGraph lhss

{-- letGroup [NamedTerm n def] t = LetInTerm (NamedTerm n def) t
letGroup (n:ns) t = LetInTerm n $ letGroup ns t
letGroup [] _ = error "Provide at least one named term."  --}
