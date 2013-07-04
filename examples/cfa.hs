module CFA where

data Nat = Zero | Succ Nat

data List = Nil | Cons Nat List

foldl f init list = case list of
    Nil         -> init
    (Cons x xs) -> f x (foldl f init xs)

foldr f init list = case list of
    Nil         -> init
    (Cons x xs) -> f (foldr f init xs) x

main = foldr
