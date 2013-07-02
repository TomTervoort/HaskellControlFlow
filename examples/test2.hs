{-# LANGUAGE Haskell2010 #-}

module Foo where


data A = B Integer | C

main = let abc a = case a of
                       B x -> 42 * x
                       C -> 2
        in abc C