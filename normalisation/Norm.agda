module Norm where

-- This module contains a normal form for our numbers (Lemma 4.2), and proof
-- that if two nat functions are extensionally equal for inputs 0, 1, 2 then the
-- normal forms must be the same (Theorem 4.3)!

{- Standard machinery that isn't specific to our language of numerical expressions.
   * Definition of natural numbers and some convenient operations on them
   * Propositional equality with some helpers
   * Datatypes with Zero and One inhabitants
-}
module Basics where
  data Nat : Set where
    ze : Nat
    su : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}

  -- Addition for Nats.
  _+N_ : Nat -> Nat -> Nat
  ze   +N y = y
  su x +N y = su (x +N y)

  -- Double a Nat.
  du : Nat -> Nat
  du  ze    = ze
  du (su n) = su (su (du n))

  -- Full of a Nat.
  fu : Nat -> Nat
  fu  ze    = ze
  fu (su n) = su (du (fu n))

  -- Double a Nat `k` times.
  dus : (k : Nat) -> Nat -> Nat
  dus ze n = n
  dus (su k) n = du (dus k n)

  record One : Set where constructor <>
  data Zero : Set where

  _<=_ : Nat -> Nat -> Set
  ze <= _ = One
  su x <= ze = Zero
  su x <= su y = x <= y

  -- Propositional equality
  data _~_ {X : Set}(x : X) : X -> Set where
    r~ : x ~ x

  !~ : {X : Set} -> (x : X) -> x ~ x
  !~ _ = r~

  _~$~_ : forall {S T}{f g : S -> T} -> f ~ g -> {a b : S} -> a ~ b -> f a ~ g b
  r~ ~$~ r~ = r~

  module _ {X : Set}(x : X) where

    _~[_>_ : forall {y z} -> x ~ y -> y ~ z -> x ~ z
    _~[_>_ r~ q = q

    _<_]~_ : forall {y z} -> y ~ x -> y ~ z -> x ~ z
    _<_]~_ r~ q = q

    _[QED] : x ~ x
    _[QED] = r~

    infixr 2 _~[_>_ _<_]~_
    infixr 3 _[QED]

open Basics

mutual
  -- A strictly monotonic function of at most one variable.
  record Str : Set where
    pattern
    inductive
    constructor `2^_`*_
    field
      doubling : Nat
      operator : Opr

  -- An operation is either a variable (`X) or "full" of a strictly monotonic
  -- function (`F).
  data Opr : Set where
    `X : Opr
    `F : Str -> Opr

mutual
  -- Evaluate a strict monotone function at a given Nat.
  evStr : Str -> Nat -> Nat
  evStr (`2^ k `* f) x = dus k (evOpr f x)

  -- Evaluate an operation at a given Nat
  evOpr : Opr -> Nat -> Nat
  evOpr `X     x = x
  evOpr (`F f) x = fu (evStr f x)

-- A function which evaluates to 0 at 0.
data F00 : Set where
  -- The function that always returns zero
  `ze  : F00
  -- Pack a strict monotone function
  `[_] : Str -> F00

-- Evaluate a `F00` function at a given Nat.
evF00 : F00 -> Nat -> Nat
evF00 `ze    _ = 0
evF00 `[ s ] x = evStr s x

-- Here is the normal form for numerical expressions proposed in Lemma 4.2.
-- `upshift` represents 0 or more successors, which are applied to either Z or
-- to a strictly monotonic function.
record Nrm : Set where
  pattern
  constructor _`+_
  field
    upshift : Nat
    fun00   : F00

-- Evaluate a numerical expression in normal form, substituting it's variable
-- with `x` if appropriate.
evNrm : Nrm -> Nat -> Nat
evNrm (n `+ f) x = n +N evF00 f x

-- The identity function in our normal form.
id! : Nrm
id! = 0 `+ `[ `2^ 0 `* `X ]

-- The constant 0 function in our normal form.
ze! : Nrm
ze! = 0 `+ `ze

-- Take the successor of a numerical expression preserving normal form, by
-- adding one to the constant upshift.
su! : Nrm -> Nrm
su! (n `+ f) = su n `+ f

-- Double a F00.
d00 : F00 -> F00
d00 `ze = `ze
d00 `[ `2^ n `* f ] = `[ `2^ su n `* f ]

-- Double a numerical expression, preserving normal form by doubling the
-- constant upshift and doubling the F00 function.
du! : Nrm -> Nrm
du! (n `+ f) = du n `+ d00 f

-- full (a + b) = full a + 2^a * full b
fuHelp : Nat -> F00 -> F00
fuHelp _ `ze = `ze
fuHelp a `[ b ] = `[ `2^ a `* `F b ]

-- Take 'full' of a numerical expression preserving normal form.
fu! : Nrm -> Nrm
fu! (a `+ b) = fu a `+ fuHelp a b

-- The identity function returns its input.
idLem : forall x -> evNrm id! x ~ x
idLem x = r~

-- The constant zero function always returns 0.
zeLem : forall x -> evNrm ze! x ~ 0
zeLem x = r~

-- Evaluating the successor of `f` is the same as taking the successor of
-- evaluating `f`.
suLem : forall f x -> evNrm (su! f) x ~ su (evNrm f x)
suLem f x = r~

-- Doubling is distributive.
duDis : forall a b -> du (a +N b) ~ (du a +N du b)
duDis ze b = r~
duDis (su a) b = !~ su ~$~ (!~ su ~$~ duDis a b)

-- Doubling a `F00` doubles all of the results.x
d00Lem : forall f x -> evF00 (d00 f) x ~ du (evF00 f x)
d00Lem `ze x = r~
d00Lem `[ `2^ k `* f ] x = r~

-- Evaluating doubled `f` is the same as doubling the result of evaluating `f`.
duLem : forall f x -> evNrm (du! f) x ~ du (evNrm f x)
duLem (a `+ f) x =
  (du a +N evF00 (d00 f) x) ~[ !~ (du a +N_) ~$~ d00Lem f x >
  (du a +N du (evF00 f x)) < duDis a (evF00 f x) ]~
  du (a +N evF00 f x) [QED]

fuDis : forall a b -> fu (a +N b) ~ (fu a +N dus a (fu b))
fuDis ze b = r~
fuDis (su a) b = !~ su ~$~ (
  du (fu (a +N b)) ~[ !~ du ~$~ fuDis a b >
  du (fu a +N dus a (fu b)) ~[ duDis (fu a) (dus a (fu b)) >
  (du (fu a) +N du (dus a (fu b))) [QED])

lem0dus : forall k -> dus k 0 ~ 0
lem0dus ze = r~
lem0dus (su k) = !~ du ~$~ lem0dus k

f00Lem : forall a f x -> evF00 (fuHelp a f) x ~ dus a (fu (evF00 f x))
f00Lem a `ze x = 0 < lem0dus a ]~ dus a 0 [QED]
f00Lem a `[ f ] x = r~

fuLem : forall f x -> evNrm (fu! f) x ~ fu (evNrm f x)
fuLem (a `+ f) x =
  (fu a +N evF00 (fuHelp a f) x) ~[ !~ (fu a +N_) ~$~ f00Lem a f x >
  (fu a +N dus a (fu (evF00 f x))) < fuDis a (evF00 f x) ]~
  fu (a +N evF00 f x) [QED]

_+N0 : forall n -> (n +N 0) ~ n
ze +N0 = r~
su n +N0 = !~ su ~$~ (n +N0)

-- Another implementation of equality for Nats
NatNoConf : Nat -> Nat -> Set
NatNoConf ze ze = One
NatNoConf ze (su y) = Zero
NatNoConf (su x) ze = Zero
NatNoConf (su x) (su y) = x ~ y

natNoConf : forall {x y} -> x ~ y -> NatNoConf x y
natNoConf {ze} r~ = _
natNoConf {su x} r~ = r~

leftCan : forall a {x y} -> (a +N x) ~ (a +N y) -> x ~ y
leftCan ze q = q
leftCan (su a) q = leftCan a (natNoConf q)

dui : forall {x y} -> du x ~ du y -> x ~ y
dui {ze} {ze} q = r~
dui {su x} {su y} q = !~ su ~$~ dui (natNoConf (natNoConf q))

fui : forall {x y} -> fu x ~ fu y -> x ~ y
fui {ze} {ze} q = r~
fui {su x} {su y} q = !~ su ~$~ fui (dui (natNoConf q))

-- Now we intend to prove validatity of normal forms by reasoning about the
-- behaviour of our data structures when evaluated at 0, 1 and 2 (Theorem 4.3),
-- so we make some definitions to show what to expect at each of these inputs.

-- The "lem0" functions say that evaluating a numerical expression at 0 yields
-- the number of successors (the upshift) of the normal form.
mutual
  lem0Str : forall f -> evStr f 0 ~ 0
  lem0Str (`2^ k `* f) =
    dus k (evOpr f 0) ~[ !~ (dus k) ~$~ lem0Opr f >
    dus k 0 ~[ lem0dus k >
    0 [QED]

  lem0Opr : forall f -> evOpr f 0 ~ 0
  lem0Opr `X = r~
  lem0Opr (`F f) = !~ fu ~$~ lem0Str f

lem0F00 : forall f -> evF00 f 0 ~ 0
lem0F00 `ze = r~
lem0F00 `[ s ] = lem0Str s

lem0Nrm : forall a f -> evNrm (a `+ f) 0 ~ a
lem0Nrm a f =
  (a +N evF00 f 0) ~[ !~ (a +N_) ~$~ lem0F00 f >
  (a +N 0) ~[ a +N0 >
  a [QED]

lemDu0 : forall n -> du n ~ 0 -> n ~ 0
lemDu0 ze q = r~

lemDus0 : forall k n -> dus k n ~ 0 -> n ~ 0
lemDus0 ze n q = q
lemDus0 (su k) n q = lemDus0 k n (lemDu0 (dus k n) q)

lemFu0 : forall n -> fu n ~ 0 -> n ~ 0
lemFu0 ze q = r~

lemOdEv : forall n m -> su (du n) ~ du m -> Zero
lemOdEv (su n) (su m) q = lemOdEv n m (natNoConf (natNoConf q))

-- Full only yields an even number for `full(0) = 0`
lemFuDu : forall n m -> fu n ~ du m -> n ~ 0
lemFuDu ze m q = r~
lemFuDu (su n) m q with () <- lemOdEv (fu n) m q

-- What happens when our structures are evaluated at 1.
mutual
  str1su : forall f -> evStr f 1 ~ 0 -> Zero
  str1su (`2^ k `* f) q = opr1su f (lemDus0 k (evOpr f 1) q)

  opr1su : forall f -> evOpr f 1 ~ 0 -> Zero
  opr1su (`F f) q = str1su f (lemFu0 (evStr f 1) q)

mutual

  opr1od : forall f n -> evOpr f 1 ~ du n -> Zero
  opr1od `X ze ()
  opr1od `X (su n) ()
  opr1od (`F f) n q = str1su f (lemFuDu (evStr f 1) n q)


-- "full" can never yield 2
fu2 : forall n -> fu n ~ 2 -> Zero
fu2 (su ze) ()
fu2 (su (su n)) ()

mutual
  -- Strict monotone functions are equal if they agree below three
  claimStr :  forall f g
    -> ((x : Nat) -> x <= 2 -> evStr f x ~ evStr g x)
    -> f ~ g
  claimStr (`2^ ze `* f) (`2^ ze `* g) q = !~ (`2^ 0 `*_) ~$~ claimOpr f g q
  claimStr (`2^ ze `* f) (`2^ su l `* g) q with () <- opr1od f _ (q 1 <>)
  claimStr (`2^ su k `* f) (`2^ ze `* g) q with () <- opr1od g _ (_ < q 1 <> ]~ _ [QED])
  claimStr (`2^ su k `* f) (`2^ su l `* g) q
    with r~ <- claimStr (`2^ k `* f) (`2^ l `* g) (\ x p -> dui (q x p))
    = r~

  -- Operations are equal if they agree below three
  claimOpr : forall f g
    -> ((x : Nat) -> x <= 2 -> evOpr f x ~ evOpr g x)
    -> f ~ g
  claimOpr `X `X q = r~
  claimOpr `X (`F g) q with () <- fu2 (evStr g 2) (_ < q 2 <> ]~ _ [QED])
  claimOpr (`F f) `X q with () <- fu2 (evStr f 2) (q 2 <>)
  claimOpr (`F f) (`F g) q = !~ `F ~$~ claimStr f g \ x p -> fui (q x p)

-- F00s are equal if they agree below three
claimF00 : forall f g
  -> ((x : Nat) -> x <= 2 -> evF00 f x ~ evF00 g x)
  -> f ~ g
claimF00 `ze `ze q = r~
claimF00 `ze `[ g ] q with () <- str1su g (evStr g 1 < q 1 <> ]~ 0 [QED])
claimF00 `[ f ] `ze q with () <- str1su f (q 1 <>)
claimF00 `[ f ] `[ g ] q = !~ `[_] ~$~ claimStr f g q

-- This is the proof of Theorem 4.3 (Agree Below Three)
-- If numbers `f` and `g` produce the same outputs for 0 <= x <= 2,
-- they agree for all values of x
claimNrm : forall f g
  -> ((x : Nat) -> x <= 2 -> evNrm f x ~ evNrm g x)
  -> f ~ g
claimNrm (a `+ f) (b `+ g) q
  with r~ <- a < lem0Nrm a f ]~ evNrm (a `+ f) 0 ~[ q 0 <> > evNrm (b `+ g) 0 ~[ lem0Nrm b g > b [QED]
  = !~ (a `+_)
  ~$~ claimF00 f g \ x p -> leftCan a (q x p)

-- An unnormalised numerical expression
data Fun : Set where
  `ze `id : Fun
  `su `du `fu : Fun -> Fun

-- Take the normal form of a `Fun`
nm : Fun -> Nrm
nm `ze = ze!
nm `id = id!
nm (`su f) = su! (nm f)
nm (`du f) = du! (nm f)
nm (`fu f) = fu! (nm f)

-- Evaluate a numerical expression at a given Nat
ev : Fun -> Nat -> Nat
ev `ze n = 0
ev `id n = n
ev (`su f) n = su (ev f n)
ev (`du f) n = du (ev f n)
ev (`fu f) n = fu (ev f n)

-- Lemma: evaluating a numerical expression yields the same result at all values
-- of `x` as evaluating its normal form.
nmLem : forall f x -> evNrm (nm f) x ~ ev f x
nmLem `ze x = zeLem x
nmLem `id x = idLem x
nmLem (`su f) x =
  evNrm (su! (nm f)) x ~[ suLem (nm f) x >
  su (evNrm (nm f) x) ~[ !~ su ~$~ nmLem f x >
  su (ev f x) [QED]
nmLem (`du f) x =
  evNrm (du! (nm f)) x ~[ duLem (nm f) x >
  du (evNrm (nm f) x) ~[ !~ du ~$~ nmLem f x >
  du (ev f x) [QED]
nmLem (`fu f) x =
  evNrm (fu! (nm f)) x ~[ fuLem (nm f) x >
  fu (evNrm (nm f) x) ~[ !~ fu ~$~ nmLem f x >
  fu (ev f x) [QED]

thm : forall f g
  -> (forall x -> x <= 2 -> ev f x ~ ev g x)
  -> forall x -> ev f x ~ ev g x
thm f g q x =
  ev f x < nmLem f x ]~
  evNrm (nm f) x ~[ !~ (\ k -> evNrm k x) ~$~ claimNrm (nm f) (nm g)
      (\ y p ->
        evNrm (nm f) y ~[ nmLem f y >
        ev f y ~[ q y p >
        ev g y < nmLem g y ]~
        evNrm (nm g) y [QED])
      >
  evNrm (nm g) x ~[ nmLem g x >
  ev g x [QED]
