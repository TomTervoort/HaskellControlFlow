{-# LANGUAGE Haskell2010 #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- Largely stolen from StateT.
module Data.Fresh where

import Control.DeepSeq
import Control.Monad.Trans.State

class {- (Applicative m, Eq v) => -} Fresh m v | m -> v where
    -- | Generates a unique value.
    --
    -- > ((==) <$> fresh <*> fresh) = (const . const $ False) <$> fresh <*> fresh)
    fresh :: m v

type FreshT v m = StateT v m
runFreshT :: FreshT v m a -> v -> m (a, v)
runFreshT = runStateT

instance (NFData v, Monad m, Enum v) => Fresh (FreshT v m) v where
    fresh = StateT $ \v -> let v' = succ v in v' `deepseq` return (v, v')
