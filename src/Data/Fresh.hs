{-# LANGUAGE Haskell2010 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Fresh where

class Fresh v f where
    fresh :: f v
