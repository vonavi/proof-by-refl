(** This code re-uses pieces of code from
    http://ejcp2019.icube.unistra.fr/slides/jn_exemples_ejcp2019.v
 *)

Require Import Arith.
Require Import List.

Lemma trial : forall a b c d,
    (a + b) + (c + d) = a + b + c + d.
Proof.
  intros. repeat rewrite Nat.add_assoc. reflexivity.
Qed.

Inductive expr :=
| Var : nat -> expr
| Plus : expr -> expr -> expr.

Fixpoint interp e :=
  match e with
  | Var x => x
  | Plus a b => interp a + interp b
  end.

Ltac reify e :=
  match e with
  | ?e1 + ?e2 => let r1 := reify e1 in
                 let r2 := reify e2 in
                 constr:(Plus r1 r2)
  | _ => constr:(Var e)
  end.

Ltac matac :=
  match goal with
  | [ |- ?me1 = ?me2 ] =>
    let r1 := reify me1 in
    let r2 := reify me2 in
    change (interp r1 = interp r2)
  end.


Fixpoint flatten e :=
  match e with
  | Var x => x :: nil
  | Plus a b => flatten a ++ flatten b
  end.

Fixpoint sum_list l :=
  match l with
  | nil => 0
  | x :: r => x + sum_list r
  end.

Lemma sum_list_concat : forall l1 l2,
    sum_list l1 + sum_list l2 = sum_list (l1 ++ l2).
Proof.
  induction l1; simpl.
  - reflexivity.
  - intro l2. rewrite <- IHl1. rewrite Nat.add_assoc. reflexivity.
Qed.

Lemma flatten_correct : forall e, interp e = sum_list (flatten e).
Proof.
  induction e; simpl.
  - apply plus_n_O.
  - rewrite IHe1, IHe2. rewrite sum_list_concat. reflexivity.
Qed.

Theorem main : forall e1 e2,
    sum_list (flatten e1) = sum_list (flatten e2)
    -> interp e1 = interp e2.
Proof.
  intros. do 2 rewrite flatten_correct. assumption.
Qed.


Lemma trial_refl : forall a b c d,
    (a + b) + (c + d) = a + b + c + d.
Proof.
  intros. matac. apply main. simpl. reflexivity.
Qed.
