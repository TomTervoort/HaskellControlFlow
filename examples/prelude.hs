module Prelude where

data List = Nil | Cons Int List

{-
x || y = if x then True else y
x && y = if x then y else False

otherwise = True

not True  = False
not False = True

undefined = undefined

error str = undefined

foldr f init list = case list of
    Nil         -> init
    (Cons x xs) -> f (foldr f init xs) x
-}

foldl f init list = case list of
    Nil         -> init
    (Cons x xs) -> f x (foldl f init xs)

plus     = (+)
multiply = (*)
either   = if True then plus else multiply

sum   = foldl plus 0
mult  = foldl multiply 1
weird = foldl either 0

list = (Cons 3 (Cons 1 (Cons 2 (Cons 5 Nil))))

main = sum list + mult list
