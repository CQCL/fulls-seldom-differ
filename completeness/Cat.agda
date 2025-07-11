module Cat where

open import Basics

-- Definitions for working with the category of solutions: C01N (Definition 5.2)

data Obj : Set where
  `0 `1 `N : Obj

FObj : Obj -> Set
FObj `0 = Zero
FObj `1 = One
FObj `N = Nat

-- The embedding of C01N arrows into Set
record _>>_ (S T : Obj) : Set where
  constructor go
  field
    fo : FObj S -> FObj T
open _>>_ public

FARR : (A : Obj -> Obj -> Set) -> Set
FARR A = forall {S T} -> A S T -> S >> T
-- Mia Farra borra marra furra farra!

-- Identity arrow
iA : forall {X} -> X >> X
iA = go id

-- Arrow from the initial object `1 to any object
eA : forall {X} -> FObj X -> `1 >> X
eA x = go (K- x)

-- The "no solution" arrow, represented in the paper by an upside down question mark
nA : forall {X} -> `0 >> X
nA = go magic

-- Composition of arrows
_->-_ : forall {R S T} -> R >> S -> S >> T -> R >> T
go f ->- go g = go (f - g)

-- Injectivity of arrows
Inj : forall {X Y} -> X >> Y -> Set
Inj f = forall {a b} -> fo f a ~ fo f b -> a ~ b

-- Show that two arrows are equal
_~><~_ : forall {S T} -> S >> T -> S >> T -> Set
go f ~><~ go g = forall x -> f x ~ g x

-- Two arrows from the same object, composed with an injective arrow, are equal
injCo : forall {R S T}{f0 f1 : R >> S}{g : S >> T}
  -> Inj g
  -> (f0 ->- g) ~><~ (f1 ->- g)
  -> f0 ~><~ f1
injCo gi q x = gi (q x)

module _ {S T : Obj} where
  _~!_>_ : forall (f : S >> T){g h} -> f ~><~ g -> g ~><~ h -> f ~><~ h
  _~!_>_ (go f) {go g} {go h} p q x = f x ~[ p x > g x ~[ q x > h x [QED]
  _<_!~_ : forall (f : S >> T){g h} -> g ~><~ f -> g ~><~ h -> f ~><~ h
  _<_!~_ (go f) {go g} {go h} p q x = f x < p x ]~ g x ~[ q x > h x [QED]
  _[==] : (f : S >> T) -> f ~><~ f
  _[==] (go f) x = f x [QED]
  infixr 1 _~!_>_ _<_!~_
  infixr 2 _[==]

--  Composing equal arrows gets the same composition
module _ {R S T : Obj} where
  _~>~_ : {f0 f1 : R >> S}(fq : f0 ~><~ f1)
       -> {g0 g1 : S >> T}(gq : g0 ~><~ g1)
       -> (f0 ->- g0) ~><~ (f1 ->- g1)
  (fq ~>~ gq) x rewrite fq x = gq _

-- Composing a list of arrows of the same kind, for chaining S,F,D. The Nat is
-- used to count the arrows in the list
data _-[_/_]-_ (R : Obj)(A : Obj -> Obj -> Set)
  : Nat -> Obj -> Set where
  [] : R -[ A / ze ]- R
  _-,_ : forall {S T n} -> R -[ A / n ]- S -> A S T
      -> R -[ A / su- n ]- T

infixl 10 _-,_

-- Compose a sequence of arrows
ncomp : forall {n A} -> FARR A -> FARR (_-[ A / n ]-_)
ncomp fa [] = iA
ncomp fa (as -, a) = ncomp fa as ->- fa a

map : forall {A B n S T}
  -> (forall {S T} -> A S T -> B S T)
  -> S -[ A / n ]- T -> S -[ B / n ]- T
map ab [] = []
map ab (as -, a) = map ab as -, ab a

map-ncomp : forall {A B}
  (fa : FARR A)(fb : FARR B)
  (ab : forall {S T} -> A S T -> B S T)
  -> (forall {S T}(a : A S T) -> fa a ~><~ fb (ab a))
  -> forall {n S T}(as : S -[ A / n ]- T) -> ncomp fa as ~><~ ncomp fb (map ab as)
map-ncomp fa fb ab q [] = _ [==]
map-ncomp fa fb ab q (as -, a) = map-ncomp fa fb ab q as ~>~ q a

_++_ : forall {n m A R S T}
  -> R -[ A / n ]- S
  -> S -[ A / m ]- T
  -> R -[ A / (m +N n) ]- T
fs ++ [] = fs
fs ++ (gs -, g) = (fs ++ gs) -, g

catComp : forall {n m A R S T}(fa : FARR A)
  (fs : R -[ A / n ]- S)
  (gs : S -[ A / m ]- T)
  ->  (ncomp fa fs ->- ncomp fa gs) ~><~
      ncomp fa (fs ++ gs)
catComp fa fs [] = ncomp fa fs [==]
catComp fa fs (gs -, g) = catComp fa fs gs ~>~ (fa g [==])

_-[_]-_ : Obj -> (Obj -> Obj -> Set) -> Obj -> Set
S -[ A ]- T = Nat >< \ n -> S -[ A / n ]- T

nil : forall {A T} -> T -[ A ]- T
nil = ze , []

one : forall {A S T} -> A S T -> S -[ A ]- T
one f = su- ze , ([] -, f)

lcomp : forall {A} -> FARR A -> FARR (_-[ A ]-_)
lcomp fa (n , fs) = ncomp {n} fa fs

record _&_ (A B : Obj -> Obj -> Set)(R T : Obj) : Set where
  constructor _-&-_
  field
    {middle} : Obj
    pre : A R middle
    post : B middle T
open _&_ public

_&&_ : forall {A B} -> FARR A -> FARR B -> FARR (A & B)
(fa && fb) (a -&- b) = fa a ->- fb b
  
