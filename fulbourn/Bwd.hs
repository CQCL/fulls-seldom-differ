module Bwd where

data Bwd a = B0 | Bwd a :< a
 deriving (Eq, Foldable, Functor, Show, Traversable)

-- "Fish" concatenates a Bwd with a list, adding the list elements on the right
-- note that the operator spells out the direction of it's arguments and output
(<><) :: Bwd a -> [a] -> Bwd a
zx <>< [] = zx
zx <>< (x:xs) = zx :< x <>< xs

-- "Chips" does the same thing as fish, but concatenates by adding the Bwd
-- elements to the left of the list argument
(<>>) :: Bwd a -> [a] -> [a]
B0 <>> xs = xs
(zx :< x) <>> xs = zx <>> (x:xs)

index :: Eq a => Bwd a -> a -> Int
index (zx :< x) y
 | x == y = 0
 | otherwise = 1 + index zx y
