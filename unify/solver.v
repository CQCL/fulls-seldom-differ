Require Import Nat PeanoNat Lia Program.Tactics.


(* Our language of terms *)
Inductive term := V | Z | S' (t: term) | D (t: term) | B (t: term) | F (t: term).

(* Evaluation `t(x)` of a term at point x *)
Fixpoint eval (t: term) (x: nat) : nat := match t with
  | V => x
  | Z => 0
  | S' t => S (eval t x)
  | D t => 2 * eval t x
  | B t => 1 + 2 * eval t x
  | F t => 2 ^ (eval t x) - 1
end.

(* Term composition with `(t ∘ s)(x) = t(s(x))` *)
Fixpoint compose (t: term) (s : term) : term := match t with
  | V => s
  | Z => Z
  | S' t => S' (compose t s)
  | D t => D (compose t s)
  | B t => B (compose t s)
  | F t => F (compose t s)
end.

Notation "t ∘ s" := (compose t s) (at level 50).

(* Notation for the maybe monad *)
Notation "'try' X := A 'in' B" :=
  (match A with Some X => B | None => None end)
  (at level 200, X pattern, A at level 100, B at level 200).



(* Check if a term unifies with zero.
   
   Returns the unifier or `None`.
*)
Fixpoint unZ (t : term) : option term := match t with
  | V => Some Z
  | Z => Some V
  | S' t => None
  | D t => unZ t
	| B t => None
	| F t => unZ t
end.

(* Check if a term is a successor.

   Returns the predecessor and a substitution for t, or `None`.
*)
Fixpoint unS (t : term) : option (term * term) := match t with
	| V => Some (V, S' V)
  | Z => None
	| S' t => Some (t, V)
  | D t => try (p, subst) := unS t in Some (B p, subst)
	| B t => Some (D t, V)
	| F t => try (p, subst) := unS t in Some (D (F p), subst)
end.


(* Check if a term is even.

   Returns half of the value and a substitution for t, or `None`.
*)
Fixpoint unD (t : term) : option (term * term) := match t with
	| V => Some (V, D V)
  | Z => Some (Z, V)
	| S' t => try (h, subst) := unB t in Some (S' h, subst)
  | D t => Some (t, V)
	| B t => None
	| F t => try subst := unZ t in Some (Z, subst)
end


(* Check if a term is odd.

   Returns rounded-down half of the value and a substitution for t, or `None`.
*)
with unB (t : term) : option (term * term) := match t with
	| V => Some (V, B V)
	| Z => None
	| S' t => unD t
	| D t => None
	| B t => Some (t, V)
	| F t => try (p, subst) := unS t in Some (F p, subst)
end.


(* Next, we define the recursion measure for out main unification function *)

(* Count the total number of Fs and Ss in the term *)
Fixpoint FS_count (t : term) : nat := match t with
| F t => S (FS_count t)
| S' t => S (FS_count t)
| D t => FS_count t
| B t => FS_count t
| _ => 0
end.

(* Count the distance to the first F in the term *)
Fixpoint SDB_prefix (t : term) : nat := match t with
| F t => 0 
| S' t => S (SDB_prefix t)
| D t => S (SDB_prefix t)
| B t => S (SDB_prefix t)
| _ => 0
end.

(* Define the measure as a lexicographic order over these two properties  *)
Definition measure (t1 t2 : term) := (FS_count t1 + FS_count t2, SDB_prefix t1 + SDB_prefix t2).

Definition lex (p1 p2 : nat * nat) :=
  let (x1, y1) := p1 in
  let (x2, y2) := p2 in
  x1 < x2 \/ (x1 = x2 /\ y1 < y2).


(* Main unification function, defined by well-founded recursion over
   the measure defined above.

   Returns the most general unifiers s1, s2 for t1 and t2, or `None`
   if they do not unify. They satisfy (t1 ∘ s1)(x) = (t2 ∘ s2)(x) for
   all x.

   Note that we use Program here, so the Acc_inv obligations are still
   open.
*)
Program Fixpoint nunify (t1 t2 : term) (ACC : Acc lex (measure t1 t2))
  {struct ACC} : option (term * term) := match (t1, t2) with
  | (V, t2) => Some (t2, V)
  | (t1, V) => Some (V, t1)
  | (Z, t2) => try s2 := unZ t2 in Some (V, s2)
  | (t1, Z) => try s1 := unZ t1 in Some (s1, V)
  | (D h1, t2) =>
      try (h2, s2) := unD t2 in 
      try (s1, s2') := nunify h1 h2 (Acc_inv ACC _) in
      Some (s1, s2 ∘ s2')
  | (t1, D h2) =>
      try (h1, s1) := unD t1 in 
      try (s1', s2) := nunify h1 h2 (Acc_inv ACC _) in
      Some (s1 ∘ s1', s2)
  | (B h1, t2) =>
      try (h2, s2) := unB t2 in 
      try (s1, s2') := nunify h1 h2 (Acc_inv ACC _) in
      Some (s1, s2 ∘ s2')
  | (t1, B h2) =>
      try (h1, s1) := unB t1 in 
      try (s1', s2) := nunify h1 h2 (Acc_inv ACC _) in
      Some (s1 ∘ s1', s2)
  | (F t1, S' t2) =>
      try (p1, s1) := unS t1 in
      try (s1', s2) := nunify (D (F p1)) t2 (Acc_inv ACC _) in
      Some (s1 ∘ s1', s2)
  | (S' t1, F t2) =>
      try (p2, s2) := unS t2 in
      try (s1, s2') := nunify t1 (D (F p2)) (Acc_inv ACC _) in
      Some (s1, s2 ∘ s2')
  | (F t1, F t2) => nunify t1 t2 (Acc_inv ACC _)
  | (S' t1, S' t2) => nunify t1 t2 (Acc_inv ACC _)
end.


(* Below are some lemmas we need to prove termination *)

Lemma unS_FS_count t p s :
  unS t = Some (p, s) -> FS_count p <= FS_count t.
Proof.
  revert p s. induction t; cbn; intros p s H; try now inversion H.
  - inversion H. lia.
  - destruct (unS t) as [[p' s']|]; inversion H. cbn. now eapply IHt.
  - destruct (unS t) as [[p' s']|]; inversion H. cbn. now eapply le_n_S, IHt.
Qed.

Lemma unDB_FS_count t he ho se so :
  (unD t = Some (he, se) -> FS_count he <= FS_count t)
  /\
  (unB t = Some (ho, so) -> FS_count ho <= FS_count t).
Proof.
  revert he ho se so. induction t; cbn; intros he ho se so; split; intros H; try now inversion H.
  - destruct (unB t) as [[ho' so']|]; inversion H. cbn. now eapply le_n_S, IHt.
  - destruct (unD t) as [[he' se']|]; inversion H. now apply le_S, (IHt ho he so se).
  - destruct (unZ t) as [sz|]; inversion H. apply Nat.le_0_l.
  - destruct (unS t) as [[p sp]|] eqn:Hp; inversion H. cbn. 
    now apply le_n_S, unS_FS_count with (s := sp).
Qed.

Lemma unD_FS_count t h s :
  unD t = Some (h, s) -> FS_count h <= FS_count t.
Proof.
  apply (unDB_FS_count _ _ Z s Z).
Qed.

Lemma unB_FS_count t h s :
  unB t = Some (h, s)-> FS_count h <= FS_count t.
Proof.
  apply (unDB_FS_count _ Z _ Z _).
Qed.

Lemma halve_SDB_prefix t he ho se so :
  (unD t = Some (he, se) -> SDB_prefix he <= SDB_prefix t)
  /\
  (unB t = Some (ho, so)  -> SDB_prefix ho <= SDB_prefix t).
Proof.
  revert he ho se so. induction t; cbn; intros he ho se so; split; intros H; try (inversion H; try easy; lia).
  - destruct (unB t) as [[ho' so']|]; inversion H. cbn. now eapply le_n_S, IHt.
  - destruct (unD t) as [[he' se']|]; inversion H. now apply le_S, (IHt ho he so se).
  - now destruct (unZ t) as [sz|]; inversion H.
  - now destruct (unS t) as [[p sp]|]; inversion H.
Qed.

Lemma unD_SDB_prefix t h s :
  unD t = Some (h, s) -> SDB_prefix h <= SDB_prefix t.
Proof.
  apply (halve_SDB_prefix _ _ Z s Z).
Qed.

Lemma unB_SDB_prefix t h s :
  unB t = Some (h, s) -> SDB_prefix h <= SDB_prefix t.
Proof.
  apply (halve_SDB_prefix _ Z _ Z _).
Qed.


(* Tactic to inspect the goal and insert the relevant facts proved above
   into the context.
*)
Ltac find_facts := match goal with
  | [ H : unS _  = _ |- _ ] =>
      apply unS_FS_count, Nat.lt_eq_cases in H as [| ->]
  | [ H : unD _ = _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' := H);
      apply unD_SDB_prefix, Nat.lt_eq_cases in H as [| ->];
      apply unD_FS_count, Nat.lt_eq_cases in H' as [| ->]
  | [ H : unB _ = _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' := H);
      apply unB_SDB_prefix, Nat.lt_eq_cases in H as [| ->];
      apply unB_FS_count, Nat.lt_eq_cases in H' as [| ->]
  | _ => idtac
end.


(* Solve recursion obligations of nunify *)
Solve Obligations of nunify with
  program_simpl;
  try easy;
  try symmetry in Heq_anonymous;
  find_facts; cbn;
  try (left; lia);
  try (right; split; lia).


(* Bonus: More efficient version implemented using the Equations package: *)

From Equations Require Import Equations.

Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.
Notation "x 'eq:' p" := (exist _ x p) (only parsing, at level 20).

Opaque unS unD unB.

Equations? nunify_acc (t1 t2 acc1 acc2: term) : option (term * term) 
  by wf (FS_count t1 + FS_count t2, SDB_prefix t1 + SDB_prefix t2) (lexprod _ _ lt lt) :=
nunify_acc V t2 acc1 acc2 => Some (t2 ∘ acc1, acc2);
nunify_acc t1 V acc1 acc2 => Some (acc1, t1 ∘ acc2);
nunify_acc Z t2 acc1 acc2 => try s2 := unZ t2 in Some (acc1, s2 ∘ acc2);
nunify_acc t1 Z acc1 acc2 => try s1 := unZ t1 in Some (s1 ∘ acc1, acc2);
nunify_acc (D h1) t2 acc1 acc2 with inspect (unD t2) => {
  | Some (h2, s2) eq: _ => nunify_acc h1 h2 acc1 (s2 ∘ acc2)
  | None eq: _ => None
};
nunify_acc t1 (D h2) acc1 acc2 with inspect (unD t1) => {
  | Some (h1, s1) eq: _ => nunify_acc h1 h2 (s1 ∘ acc1) acc2
  | None eq: _ => None
};
nunify_acc (B h1) t2 acc1 acc2 with inspect (unB t2) => {
  | Some (h2, s2) eq: _ => nunify_acc h1 h2 acc1 (s2 ∘ acc2)
  | None eq: _ => None
};
nunify_acc t1 (B h2) acc1 acc2 with inspect (unB t1) => {
  | Some (h1, s1) eq: _ => nunify_acc h1 h2 (s1 ∘ acc1) acc2
  | None eq: _ => None
};
nunify_acc (F t1) (S' t2) acc1 acc2 with inspect (unS t1) => {
  | Some (p1, s1) eq: _ => nunify_acc (D (F p1)) t2 (s1 ∘ acc1) acc2
  | None eq: _ => None
};
nunify_acc (S' t1) (F t2) acc1 acc2 with inspect (unS t2) => {
  | Some (p2, s2) eq: _ => nunify_acc t1 (D (F p2)) acc1 (s2 ∘ acc2)
  | None eq: _ => None
};
nunify_acc (F t1) (F t2) acc1 acc2 => nunify_acc t1 t2 acc1 acc2;
nunify_acc (S' t1) (S' t2) acc1 acc2 => nunify_acc t1 t2 acc1 acc2.
Proof.
  Transparent unD unB.
  all: find_facts; cbn in *; try (left; lia); try (right; lia).
Qed.


Definition nunify_fast t1 t2 := nunify_acc t1 t2 Z Z.
