{-# LANGUAGE DataKinds, PatternSynonyms #-}

module Syntax where

import Data.Bifunctor

import Hasochism

data Nat n x = NVar (Var n x) | Zer | Suc (Nat n x) | Dub (Nat n x) | Ful (Nat n x)
 deriving (Show, Eq, Foldable, Functor, Traversable)

-- deriving instance Show x => Show (TyNatF x)

data Var n x = FV x | BV (VVar n) deriving (Eq, Foldable, Functor, Show, Traversable)

-- Type is parameterised by the number of bound variables, and the type of free variables
-- (that way round so we can get a Functor instance)
data Type n x
 = TVar (Var n x)
 | String :* [Type n x]
 | Type n x :-> Type n x
 | Type n x :^ Nat n x
 deriving (Show, Eq, Foldable, Functor, Traversable)

{-
instance Bifunctor Type where
  first f ty = case ty of
    TVar v -> TVar (f v)
    c :* tys -> c :* (first f <$> tys)
    s :-> t -> first f s :-> first f t
    t :^ n -> first f t :^ n
  second = fmap
-}

type RawType = Type Z String
type RawScheme = ([String], [RawType], RawType)  -- nat variables, inputs and output type
type RawClause = (String, Maybe [Nat Z String], [Pat String], Expr String)

data Expr a
 = EVar a
 | String :$ [Expr a]   -- data constructors
 | Expr a :/ Expr a   -- application
 | Rec String (Maybe [Nat Z a])   -- recursive function call
 | (Expr a, Pat a) :& (Expr a) -- irrefutable match on intermediate computation
 deriving (Show, Functor)

infixl 3 :/
infixr 2 :&
infixr 4 :$
infixr 4 :->

data Pat a
 = PV a
 | String :? [Pat a]
 deriving (Show, Functor)

-- Patterns for types
pattern Prod a b = "Prod" :* [a, b]
pattern Bit = "Bit" :* []
pattern Unit = "Unit" :* []

-- Patterns for terms
pattern Pair a b = "pair" :$ [a, b]
pattern Nil = "nil" :$ []
pattern Cons x xs = "cons" :$ [x, xs]
pattern TT = "tt" :$ []
pattern FF = "ff" :$ []

natArgs :: Maybe [Nat Z String] -> [a] -> [Nat Z String]
natArgs Nothing xs = const (NVar (FV "_")) <$> xs
natArgs (Just ns) _ = ns
