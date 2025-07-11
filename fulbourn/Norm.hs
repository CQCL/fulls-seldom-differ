{-# LANGUAGE DataKinds #-}

module Norm where

import Hasochism (N(..))
import Syntax hiding (Type)
import Util (nTimes)

import Control.Applicative
import Data.Kind

data VNum a = VNum { upshift :: Integer, fun00 :: Fun00 a }
 deriving (Eq, Foldable, Functor, Show)
data Fun00 a = Const0 | Strict (Mono a)
 deriving (Eq, Foldable, Functor, Show)
data Mono a = Monotone { doublings :: Integer, op :: Operator a }
 deriving (Eq, Foldable, Functor, Show)
data Operator a = NumVar a | Full (Mono a)
 deriving (Eq, Foldable, Functor, Show)

class NatNorm (t :: Type -> Type)  where
  toVNum :: t a -> VNum a

instance NatNorm Fun00 where
  toVNum = VNum 0

instance NatNorm Mono where
  toVNum = toVNum . Strict

instance NatNorm Operator where
  toVNum = toVNum . Monotone 0

vzero :: VNum a
vzero = toVNum Const0

vvar :: a -> VNum a
vvar = toVNum . NumVar

vadd :: Integer -> VNum a -> VNum a
vadd n (VNum up f00) = VNum (n + up) f00

vsucc :: VNum a -> VNum a
vsucc = vadd 1

vdoubs :: Integer -> VNum a -> VNum a
vdoubs k (VNum n f00) = VNum (2^k * n) (doubs00 f00)
 where
  doubs00 Const0 = Const0
  doubs00 (Strict (Monotone k' op)) = Strict (Monotone (k + k') op)

vdoub :: VNum a -> VNum a
vdoub = vdoubs 1

vfull :: VNum a -> VNum a
vfull (VNum n f00) = VNum (2^n - 1) (full00 f00)
 where
  full00 Const0 = Const0
  full00 (Strict mono@(Monotone k op)) = Strict (Monotone n (Full mono))

normaliseNat :: Applicative f => (a -> f (VNum a)) -> Nat Z a -> f (VNum a)
normaliseNat lup (NVar (FV x)) = lup x
normaliseNat lup Zer = pure vzero
normaliseNat lup (Suc x) = vsucc <$> normaliseNat lup x
normaliseNat lup (Dub x) = vdoub <$> normaliseNat lup x
normaliseNat lup (Ful x) = vfull <$> normaliseNat lup x

denorm :: VNum a -> Nat Z a
denorm (VNum up f00) = nTimes up Suc (denorm00 f00)
 where
  denorm00 :: Fun00 a -> Nat Z a
  denorm00 Const0 = Zer
  denorm00 (Strict mono) = denormMono mono

  denormMono (Monotone k x) = nTimes k Dub (denormOp x)

  denormOp (NumVar x) = NVar (FV x)
  denormOp (Full mono) = Ful (denormMono mono)

getVar :: VNum a -> Maybe a
getVar = foldr ((<|>) . Just) Nothing

normSubst :: VNum a -- The thing that we'll put in place of the variable
          -> VNum a -- The thing with the variable to replace
          -> VNum a
normSubst n (VNum up f00) = vadd up (subst00 f00)
 where
  subst00 Const0 = vzero
  subst00 (Strict mono) = substMono mono

  substMono (Monotone k op) = vdoubs k (substOp op)

  substOp (NumVar _) = n
  substOp (Full mono) = vfull (substMono mono)
