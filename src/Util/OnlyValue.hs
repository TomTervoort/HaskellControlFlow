module Util.OnlyValue (onlyValueFrom) where

import Data.Foldable
import Data.Monoid

-- | Just returns the only value (under Eq) contained in a @Foldable@ structure,
--   or returns @Nothing@ when there's not exactly one value.
onlyValueFrom :: (Foldable t, Eq a) => t a -> Maybe a
onlyValueFrom = toAnswer . foldMap SoFar
  where
    toAnswer (SoFar x) = Just x
    toAnswer _ = Nothing

data AllTheSame a = AllEmpty | SoFar a | Different
instance (Eq a) => Monoid (AllTheSame a) where
    mempty = AllEmpty
    mappend AllEmpty x = x
    mappend x AllEmpty = x
    mappend Different _ = Different
    mappend _ Different = Different
    mappend (SoFar x) (SoFar y)
        | x == y = SoFar x
        | otherwise = Different
