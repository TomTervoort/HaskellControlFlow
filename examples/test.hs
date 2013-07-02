{-# LANGUAGE Haskell2010 #-}

module Foo where

{-
bar = let a = 3
          b = 5
      in a * b

baz = \x y -> x + y

main = baz bar abc
    where
        abc = 3

not x = if x then False else True

data A = B a | C b

main = let abc a = case a of
                      B c -> c
                      C d -> d
       in abc (B 1)

-}

app x = x 1

main = app bar + app baz
    where
        bar x = x+3
        baz x = x*3
