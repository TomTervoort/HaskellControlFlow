module Control.Worklist where

data StepResult e a
    = Accept
    | Expand [a]
    | Reject e

done :: StepResult e a
done = Expand []

runWorklist :: (a -> StepResult e a) -> [a] -> Either e [a]
runWorklist _ [] = Right []
runWorklist f (x:xs)
    = case f x of
        Accept -> fmap (x:) (runWorklist f xs)
        Expand ys -> runWorklist f (ys ++ xs)
        Reject e -> Left e
