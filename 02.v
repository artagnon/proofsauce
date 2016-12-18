Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
  | NLeaf => S O
  | NNode tr1 _ tr2 => S (plus (nsize tr1) (nsize tr2))
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  NNode tr1 O tr2.

Theorem nsize_assoc : forall n1 n2 : nat_btree,
    S (plus (nsize n1) (nsize n2)) = nsize (nsplice n1 n2).
  destruct n1.
  destruct n2.
  unfold nsize.
  fold nsize.
  unfold nsplice.
  unfold nsize.
  reflexivity.
  unfold nsplice.
  unfold nsize; fold nsize; reflexivity.
  unfold nsplice.
  unfold nsize; fold nsize; reflexivity.
  Restart.
  induction n1; induction n2.
  unfold nsplice; unfold nsize; reflexivity.
  unfold nsplice; unfold nsize; reflexivity.
  unfold nsplice; unfold nsize; reflexivity.
  unfold nsplice; unfold nsize; reflexivity.
Qed.

Theorem demorgan_1 : forall A B : bool,
    negb (A || B) = (negb A) && (negb B).
  intros.
  destruct A.
  simpl; reflexivity.
  simpl; reflexivity.
Qed.
