Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Compute O.
Compute (S O).
Compute (S (S O)).

Fixpoint plus (n m : nat) : nat :=
  match m with
  | O => n
  | S m' => S (plus n m')
  end.

Compute (plus O (S O)).
Compute (plus (S (S O)) (S O)).

Notation "x + y" := (plus x y).
Compute ((S (S O)) + (S O)).

Fixpoint mult (n m : nat) : nat :=
  match m with
  | O => O
  | S m' => n + (mult n m')
  end.

Compute (mult (S O) (S (S O))).

Notation "x * y" := (mult x y).
Compute ((S (S O)) * (S (S O))).

Parameter G : Type.
Parameter e : G.

Parameter inv : G -> G.
Check (inv e).

Require Import Tactics.

Check forall n : Datatypes.nat, n = 2.
Check 3 = 4.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

(*
Lemma plus_O_n:
  forall n : nat,
  O + n = n.
Proof.
  intro n.
  unfold plus.
  reflexivity.
Qed.
 *)

Example and_example : (S (S O)) + (S O) = (S (S (S O))) /\  O * (S O) = O.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.