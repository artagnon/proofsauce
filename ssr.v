From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat.
From Coq Require FunctionalExtensionality Arith.PeanoNat.

Theorem dbl_implies: forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move => P Q R; move => H0 H1 a.
  exact (H1 (H0 a)).
Qed.

Theorem rev_implies (P Q R : Prop): (Q -> R) -> (P -> Q) -> P -> R.
Proof.
  move => H1 H2; apply: (dbl_implies P Q R) => //.
Qed.

Section connectives.
  Locate "_ /\ _".
  Print and.

  Theorem conj (A B : Prop): A -> B -> A /\ B.
  Proof.
    constructor 1 => //.
  Qed.

  Theorem disjunct: forall A B : Prop, A -> A \/ B.
  Proof.
      by left.
  Qed.

  Locate "~ _".

  Theorem contra (A B : Prop): (A -> B) -> ~ B -> ~ A.
  Proof.
    move => H Hq.
    move /H /Hq => //.
  Qed.

  Theorem quant A (S T: A -> Prop):
    (exists a : A, S a) -> (forall x : A, S x -> T x) -> exists b : A, T b.
  Proof.
    case => a H1 H2.
    exists a.
    apply: H2 => //.
  Qed.
End connectives.

Section rewriting.
  Definition double {A} (f : A -> A) (x : A) := f (f x).
  Fixpoint nat_iter {A} (n : nat) (f : A -> A) (x : A) :=
    if n is S n' then f (nat_iter n' f x) else x.
  Lemma double2 {A} (x : A) f t: t = double f x -> double f t = nat_iter 4 f x.
  Proof.
    move => -> => //.
  Qed.

  Check addnC.
  Print commutative.

  Definition f x y := x + y.
  Lemma comm_eq: forall x y, x + y + (y + x) = f y x + f y x.
  Proof.
    move => x y; rewrite /f; congr (_ + _). rewrite addnC => //.
  Qed.
End rewriting.
