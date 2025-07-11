module Util where

zipStrict :: [a] -> [b] -> [(a,b)]
zipStrict [] [] = []
zipStrict (a:as) (b:bs) = (a,b):zipStrict as bs

nTimes :: Integral n => n -> (a -> a) -> a -> a
nTimes 0 _ a = a
nTimes n f a
 | n < 0 = error "bad nTimes"
 | otherwise = nTimes (n - 1) f (f a)

full :: Integral n => n -> n
full n = 2^n - 1
