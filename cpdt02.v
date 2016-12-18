Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Definition left_two : nat + nat := inl _ 2.
Print left_two.

Definition left_two' := inl nat 2.
Print left_two'.

Context (A B C : Type).

Definition compose : (A -> B) -> (B -> C) -> (A -> C)
  := fun f g => (fun x => g (f x)).


Definition addtwo_or_subtractone : nat + nat -> nat
  := fun x_or_y => match x_or_y with
                     | inl x => x + 2
                     | inr y => y - 1
                   end.

Eval simpl in (addtwo_or_subtractone (inl _ 5)).

Definition swap : (A * B) -> (B * A) :=
  fun f => match f with
  | (x, y) => (y, x)
  end.

Definition mutate3 :=
  fun x y z => x * z + y.

Definition mutate3' x := mutate3 x 5 2.

Check (fun _ : False => I).

Theorem unit_singleton : forall x : unit, x = tt.
  induction x.
  reflexivity.
Qed.

Check unit_ind.

Inductive Empty_set : Set := .

Theorem empty_set_is_empty : forall x : Empty_set, 2 + 2 = 5.
  destruct 1.
Qed.

Inductive bool : Set :=
| true
| false.

Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
end.

Theorem neg_negb : forall b : bool, negb (negb b) = b.
  destruct b; reflexivity.
Qed.

Fixpoint plus (m n : nat) : nat :=
  match m with
  | O => n
  | S n' => S (plus n' n)
  end.

Theorem n_plus_O : forall n : nat, plus n O = n.
  induction n.
  reflexivity.
  induction n; crush.
Qed.

Check nat_ind.

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
  | NNil => O
  | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
  | NNil => ls2
  | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

Theorem nlength_napp :
  forall ls1 ls2 : nat_list, nlength (napp ls1 ls2)
                             = plus (nlength ls1) (nlength ls2).
  induction ls1; crush.
Qed.

Check nat_list_ind.

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
  | NLeaf => S O
  | NNode trl _ trr => plus (nsize trl) (nsize trr)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
  | NLeaf => NNode tr2 O NLeaf
  | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc : forall n1 n2 n3 : nat,
    plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
  induction n1; crush.
Qed.

Hint Rewrite n_plus_O plus_assoc.

Theorem nsize_nsplice :
  forall tr1 tr2 : nat_btree, nsize (nsplice tr1 tr2)
                              = plus (nsize tr2) (nsize tr1).
  induction tr1; crush.
Qed.

Check nat_btree_ind.