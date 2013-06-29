data Trit = Neg | Zer | Pos

add Zer x = (Zer, x)
add Neg Neg = (Neg, Zer)
add Pos Pos = (Pos, Zer)
add _ _ = (Zer, Zer)

negate Neg = Pos
negate Zer = Zer
negate Pos = Neg

subtract x y = add x (negate y)

multiply Neg x = negate x
multiply Zer _ = Zer
multiply Pos x = x
