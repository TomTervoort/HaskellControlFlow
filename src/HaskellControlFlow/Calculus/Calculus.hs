{-# LANGUAGE Haskell2010 #-}

module HaskellControlFlow.Calculus.Calculus where

import Control.Arrow
import Data.Graph
import Data.List
import Data.Maybe

import Debug.Trace

-- | Graph of mutual calls within a group of let's. The outgoing edge list may contain names that 
--   are not present in the graph. These should be ignored.
type CallGraph = [(Term (), Name, [Name])]

-- | Terms.
data Term a = LiteralTerm       a Literal
            | VariableTerm      a Name
            | HardwiredTerm     a HardwiredValue
            | ApplicationTerm   a (Term a) (Term a)
            | AbstractionTerm   a Name (Term a)
            | LetInTerm         a Name (Term a) (Term a)
            | CaseTerm          a (Term a) [(Pattern, Term a)]
            | FixTerm           a (Term a)
              deriving (Show)

data HardwiredValue
    = HwTupleCon Int
    | HwListCons
    | HwListNil

instance Show HardwiredValue where
    show (HwTupleCon n) = "(" ++ replicate n ',' ++ ")"
    show HwListCons = "(:)"
    show HwListNil = "[]"

annotation :: Term a -> a
annotation term_ = case term_ of
    LiteralTerm     a _     -> a
    VariableTerm    a _     -> a
    HardwiredTerm   a _     -> a
    ApplicationTerm a _ _   -> a
    AbstractionTerm a _ _   -> a
    LetInTerm       a _ _ _ -> a
    CaseTerm        a _ _   -> a
    FixTerm         a _     -> a

shallowMapAnnotation :: (a -> a) -> Term a -> Term a
shallowMapAnnotation f term_ = case term_ of
    LiteralTerm     ann c       -> LiteralTerm (f ann) c
    VariableTerm    ann n       -> VariableTerm (f ann) n
    HardwiredTerm   ann h       -> HardwiredTerm (f ann) h
    ApplicationTerm ann lhs rhs -> ApplicationTerm (f ann) lhs rhs
    AbstractionTerm ann bnd trm -> AbstractionTerm (f ann) bnd trm
    LetInTerm   ann bnd tm1 tm2 -> LetInTerm (f ann) bnd tm1 tm2
    CaseTerm        ann scr mtc -> CaseTerm (f ann) scr mtc
    FixTerm         ann trm     -> FixTerm (f ann) trm

-- | Patterns within case-expressions.
data Pattern = Variable Name
             | Pattern {ctorName :: Name, ctorArgs :: [Name]}
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

instance Functor Term where
    fmap f term_ = case term_ of
        LiteralTerm     ann c       -> LiteralTerm (f ann) c
        VariableTerm    ann n       -> VariableTerm (f ann) n
        HardwiredTerm   ann h       -> HardwiredTerm (f ann) h
        ApplicationTerm ann lhs rhs -> ApplicationTerm (f ann) (fmap f lhs) (fmap f rhs)
        AbstractionTerm ann bnd trm -> AbstractionTerm (f ann) bnd (fmap f trm)
        LetInTerm   ann bnd tm1 tm2 -> LetInTerm (f ann) bnd (fmap f tm1) (fmap f tm2)
        CaseTerm        ann scr mtc -> CaseTerm (f ann) (fmap f scr) (fmap (second (fmap f)) mtc)
        FixTerm         ann trm     -> FixTerm (f ann) (fmap f trm)

-- | `replaceVar a b t` replaces each occurence of a variable named `a` within `t` with `b`.
replaceVar :: Name -> Term a -> Term a -> Term a
replaceVar from to = rep
 where rep t = 
        case t of
         LiteralTerm ann c                           -> LiteralTerm ann c
         VariableTerm ann v              | v == from -> to
                                         | otherwise -> VariableTerm ann v
         HardwiredTerm ann h                         -> HardwiredTerm ann h
         ApplicationTerm ann l r                     -> ApplicationTerm ann (rep l) (rep r)
         AbstractionTerm ann n b         | n == from -> AbstractionTerm ann n b -- Name is shadowed.
                                         | otherwise -> AbstractionTerm ann n (rep b)
         LetInTerm ann n a b             | n == from -> LetInTerm ann n a b
                                         | otherwise -> LetInTerm ann n (rep a) (rep b)
         CaseTerm ann e as                           -> CaseTerm ann (rep e) (map repAlt as)
         FixTerm ann f                               -> FixTerm ann (rep f)
       
       repAlt p@(Variable n, t)   | n == from = p
                                  | otherwise = (Variable n, rep t)
       repAlt p@(Pattern c as, t) | from `elem` as = p
                                  | otherwise = (Pattern c as, rep t) 

makeCallGraph :: [(Name, Term ())] -> CallGraph
makeCallGraph = map (\(n, t) -> (t, n, names t))
 where names t = 
        case t of
         LiteralTerm _ _ -> []
         VariableTerm _ n -> [n]
         HardwiredTerm _ _ -> []
         ApplicationTerm _ l r -> names l ++ names r
         AbstractionTerm _ n b -> removeAll n $ names b -- Do not include the scoped variable.
         LetInTerm _ n t1 t2 -> removeAll n $ names t1 ++ names t2
         CaseTerm _ e as -> names e ++ concatMap altNames as
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
fixRecursion :: CallGraph -> [(Name, Term ())]
fixRecursion = concatMap handleSCC . stronglyConnCompR
 where handleSCC (AcyclicSCC (t, n, _)) = [(n, t)]
       handleSCC (CyclicSCC ns) = uncurry (++) $ unzip $ map (handleNode $ map middle ns) ns
       middle (_,x,_) = x
       absName n = "@" ++ n ++ "@"

       handleNode :: [Name] -> (Term (), Name, [Name]) -> ((Name, Term ()), (Name, Term ()))
       handleNode group (t, name, _) = ((absName name, abstracted group), 
                                        (name        , fixed 0 nameIndex))
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

namedTermsToLets :: [(Name, Term ())] -> Term () -> Term ()
namedTermsToLets = foldr (\(n, t) -> (LetInTerm () n t .)) id

-- | Smart constructor for multiple let-terms following each other in an expression.
--   The lets may refer to each other, because this function will handle ordening and (mutual) 
--   recursion.
letGroup :: [(Name, Term ())] -> Term () -> Term ()
letGroup lhss = namedTermsToLets $ fixRecursion $ makeCallGraph lhss
