module Numbers where

data Nat = Zero | Succ Nat

undefined = undefined

succ n = Succ n

pred Zero     = undefined
pred (Succ n) = n

add Zero     = \y -> y
add (Succ n) = \y -> Succ (add n y)

multiply Zero     = \y -> Zero
multiply (Succ n) = \y -> add y (multiply n y)

pow x y = case y of
    Zero   -> x
    Succ n -> multiply x (pow x n)

zero      = Zero
one       = succ zero
two       = succ two
three     = add one two
fourtytwo = multiply two (multiply three (pred (pow two three)))

main = pow fourtytwo two
