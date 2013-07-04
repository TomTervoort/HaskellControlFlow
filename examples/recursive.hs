module Recursive where

foo x = bar (x + 1)
bar x = foo (x - 1)
main  = foo (bar 5)
