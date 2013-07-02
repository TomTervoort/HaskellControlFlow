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
-}

data A = B | C

main = let abc a b = 1
       in abc 1 3

