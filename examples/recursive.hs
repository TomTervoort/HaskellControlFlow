

foo x = bar (x + 1)
bar x = foo (x - 1)
zzz = foo (bar 5)

main = 1 * 3