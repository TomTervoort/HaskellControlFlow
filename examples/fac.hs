

data Nat = Zero | Succ Nat

toInt Zero = 0
toInt (Succ n) = toInt n + 1

fac Zero = 1
fac (Succ n) = (toInt (Succ n)) * fac n

main = fac