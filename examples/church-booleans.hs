true    t f = t
false   t f = f
or      lhs rhs t f = lhs t (rhs t f)
and     lhs rhs t f = lhs (rhs t f) f
not     arg t f = arg f t

main = and true false `or` not false
