{-# LANGUAGE DataKinds, GADTs, StarIsType #-}

module Hasochism where

import Data.Kind (Type)
import Data.Type.Equality

data Ze deriving (Show, Eq)
data Su x = Ze | Su x deriving (Show, Eq, Functor)
newtype Mu f = Mu { mu :: f (Mu f) }
type Suu = Mu Su

-- TODO: Stick to one nat encoding or the other
data N = Z | S N deriving (Eq, Show)

data Ny :: N -> Type where
  Zy :: Ny Z
  Sy :: Ny n -> Ny (S n)

data Stack a :: N -> Type where
  S0 :: Stack a Z
  (:<<) :: Stack a n -> a -> Stack a (S n)

data VVar :: N -> Type where
  VZ :: VVar (S n)
  VS :: VVar n -> VVar (S n)

deriving instance Eq (VVar n)
deriving instance Show (VVar n)

data Some (t :: a -> Type) :: Type where
  Some :: t a -> Some t

data (:*:) (s :: a -> Type) (t :: a -> Type) :: a -> Type where
  (:*:) :: s x -> t x -> (s :*: t) x

infix 3 :*:

natEqOrBust :: Ny n -> Ny m -> Maybe (n :~: m)
natEqOrBust Zy Zy = Just Refl
natEqOrBust (Sy x) (Sy y) = case natEqOrBust x y of
  Just Refl -> Just Refl
  Nothing -> Nothing
natEqOrBust _ _ = Nothing

toStk :: [a] -> Some (Ny :*: Stack a)
toStk [] = Some (Zy :*: S0)
toStk (x:xs) = case toStk xs of
  Some (ny :*: stk) -> Some (Sy ny :*: stk :<< x)

(!!!) :: Stack a i -> VVar i -> a
(_ :<< x) !!! VZ = x
(zx :<< x) !!! (VS v) = zx !!! v
