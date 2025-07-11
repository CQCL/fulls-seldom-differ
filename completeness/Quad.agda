module Quad where

open import Basics
open import Cat
open import Pub

module _ {B* A A* B}
  (fb* : FARR B*)(fa : FARR A)(fa* : FARR A*)(fb : FARR B) where

  -- A Quadrifier is how we show we find most general solutions of equations.
  -- Given the top and left arrows (c.f. the start of Section 5 in the paper),
  -- We can come up with an object `S` and arrows from that to the sources of
  -- `f` and `g`, constructing the pullback.
  Quadrifier : Set
  Quadrifier = forall {P Q R}(f : A P R)(g : B Q R)
    -> Obj >< \ S -> B* S P >< \ g* -> A* S Q >< \ f*
    -> Pub[ fb* g* > fa f ]~[ fa* f* > fb g ]

module _ {B* A A* B}
  {fb* : FARR B*}{fa : FARR A}{fa* : FARR A*}{fb : FARR B}
  (r : Quadrifier fb* fa fa* fb) where

  qflip : Quadrifier fa* fb fb* fa
  qflip g f with _ , g* , f* , p <- r f g = _ , f* , g* , pubFlip p

module _ {A B}(fa : FARR A)(fb : FARR B) where

  -- A Rectifier shows we can solve equations with the property that the kinds
  -- of arrows used match on opposite sides of the square.
  Rectifier : Set
  Rectifier = Quadrifier fb fa fa fb

module _ {B* A B}
  {fb* : FARR B*}{fa : FARR A}{fb : FARR B}
  (r : Quadrifier fa fb* fb fa) where

  qstrip : forall {n} ->
    Quadrifier fa (ncomp {n} fb*) (ncomp {n} fb) fa
  qstrip [] g = _ , g , [] , pubId _
  qstrip (fs -, f) g0
    with _ , g1 , f* , p1 <- r f g0
    with _ , g2 , fs* , p2 <- qstrip fs g1
    = _ , g2 , (fs* -, f*) , pubCo p2 p1

module _ {A B}{fa : FARR A}{fb : FARR B}
  (r : Rectifier fa fb) where

  rect : forall {n m} -> Rectifier (ncomp {n} fa) (ncomp {m} fb)
  rect = qstrip (qflip (qstrip (qflip r)))
