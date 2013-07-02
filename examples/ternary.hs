data Trit = Neg | Zer | Pos

add Zer x = (Zer, x)
add Neg x = case x of 
               Neg -> (Neg, Zer)
               o   -> (Zer,Zer)
add Pos x = case x of
               Pos -> (Pos, Zer)
               o   -> (Zer, Zer)
add a b = (Zer, Zer)

negate Neg = Pos
negate Zer = Zer
negate Pos = Neg

subtract x y = add x (negate y)

multiply Neg x = negate x
multiply Zer o = Zer
multiply Pos x = x

main = multiply Neg Pos