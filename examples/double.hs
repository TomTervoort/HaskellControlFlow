module Double where

data A = B Integer Integer | C | D

makeDouble = fromIntegral

main = abc (B 1 2) where abc a = case a of
                                  B x y -> makeDouble (42 * -x + y)
                                  C -> 2.4
