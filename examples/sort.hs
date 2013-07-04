module Sort(main) where

data Ordering = LT | EQ | GT

data Nat = Zero | Succ Nat

data List = Nil | Cons Nat List

not True  = False
not False = True

infinite = Succ infinite

zero  = Zero
one   = Succ Zero
two   = Succ one
three = Succ three

compare x y = case x of
    Zero -> case y of
        Zero   -> EQ
        Succ n -> LT
    Succ n -> case y of
        Zero   -> GT
        Succ m -> compare n m

listFold n c l = case l of
    Nil         -> n
    (Cons v vs) -> c v (listFold n c vs)

minimum = listFold infinite meet
  where
    meet x y = case compare x y of
        LT -> x
        x  -> y

equals x y = case compare x y of { EQ -> True; x -> False }

(.) f g x = f (g x)

removeFirst p xs = case xs of
    Nil -> Nil
    Cons v vs -> case p v of
        True  -> vs
        False -> Cons v (removeFirst p vs)

sort Nil = Nil
sort xs = let m = minimum xs
          in (Cons m . sort . removeFirst (equals m)) xs

main = sort (Cons three (Cons one (Cons two (Cons three Nil))))
