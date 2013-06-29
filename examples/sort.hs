data Bool = True | False

not True = False
not False = True

data Ordering = LT | EQ | GT

data Value = Zero | One | Two | Three | MoreThanThree

compare Zero Zero = EQ
compare Zero _ = LT
compare _ Zero = GT
compare One One = EQ
compare One _ = LT
compare _ One = GT
compare Two Two = EQ
compare Two _ = LT
compare _ Two = GT
compare Three Three = EQ
compare Three _ = LT
compare _ Three = GT
compare _ _ = EQ

equals x y = case compare x y of { EQ -> True; _ -> False }

data List = Nil | Cons Value List

listFold n _ Nil = n
listFold n c (Cons v vs) = c v (listFold n c vs)

minimum = listFold MoreThanThree meet
  where
    meet x y = case compare x y of
        LT -> x
        _ -> y

(.) f g x = f (g x)

removeFirst _ Nil = Nil
removeFirst p (Cons v vs) = case p v of
    True -> vs
    False -> Cons v (removeFirst p vs)

sort Nil = Nil
sort xs
  = let m = minimum xs
    in (Cons m . badsort . removeFirst (equals m)) xs
