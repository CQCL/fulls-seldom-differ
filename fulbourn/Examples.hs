module Examples where

import Syntax
import Dynamics
import Parser
import GHC.TopHandler (runIO)

class Handy f where
  list :: [f x] -> f x
  (-&-) :: f x -> f x -> f x
  (=&=) :: f x -> f x -> f x
  (=%=) :: f x -> f x -> f x

instance Handy Expr where
  list [] = "nil" :$ []
  list (x : xs) = "cons" :$ [x, list xs]
  a -&- b = "pair" :$ [a, b]
  a =&= b = "even" :$ [a, b]
  a =%= b = "riffle" :$ [a, b]

instance Handy Pat where
  list [] = "nil" :? []
  list (x : xs) = "cons" :? [x, list xs]
  a -&- b = "pair" :? [a, b]
  a =&= b = "even" :? [a, b]
  a =%= b = "riffle" :? [a, b]

class Mk t where
  mk :: Expr String -> t

instance Mk (Expr String) where
  mk = id

instance Mk t => Mk (Expr String -> t) where
  mk f a = mk (f :/ a)

instance Mk t => Mk (String -> t) where
  mk f a = mk (f :/ EVar a)

myParsedGlobs = runIO (parseFile "examples.txt")

mkNum :: Int -> Int -> Expr String
mkNum n i = go n i ("nil" :$ []) where
  go 0 _ e = e
  go n i e = let (j, b) = divMod i 2 in
    go (n - 1) j ("cons" :$ [(if b == 1 then "tt" else "ff") :$ [] , e])
