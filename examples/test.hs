{-# LANGUAGE Haskell2010 #-}

module Foo where


bar = let a = 3
          b = 5
      in multiply a b

main = add abc 14
    where
        abc = 3

baz = \x y -> add x y

not x = if x then False else True

