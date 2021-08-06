Require Import Bool.
Require Import Arith.


(** This part re-uses code from
    http://ejcp2019.icube.unistra.fr/slides/jn_exemples_ejcp2019.v
 *)

Inductive is_even : nat -> Prop :=
| even_O : is_even O
| even_SS : forall x, is_even x -> is_even (S (S x)).

Lemma titi : is_even 1000.
Proof.
  Time repeat constructor.
Qed.

Print titi.

Fixpoint check_is_even (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n) => check_is_even n
  end.

Theorem nat_2_ind : forall P : nat -> Prop,
    P 0 -> P 1 -> (forall n : nat, P n -> P (S (S n))) -> forall n : nat, P n.
Proof.
  intros P H0 H1 Hrec n. cut (P n /\ P (S n)).
  - tauto.
  - induction n; intuition.
Qed.

Theorem soundness : forall n : nat, check_is_even n = true -> is_even n.
Proof.
  apply (nat_2_ind (fun n => check_is_even n = true -> is_even n)).
  - intro H. apply even_O.
  - intro H. simpl in H. discriminate.
  - intros n HI H. apply even_SS. apply HI. simpl in H. assumption.
Qed.

Lemma titi2 : is_even 1000.
Proof.
  apply soundness. Time reflexivity.
Qed.

Print titi2.


(** The example (without proofs) is taken from J. Gross et al.
    "Reification by Parametricity: Fast Setup for Proof by Reflection,
    in Two Lines of Ltac", 2018; see
    http://adam.chlipala.net/papers/ReificationITP18
 *)

Lemma check_is_even_sum (n1 n2 : nat) :
  check_is_even (n1 + n2) = negb (xorb (check_is_even n1) (check_is_even n2)).
Proof.
  case_eq (check_is_even n1); intro.
  - rewrite xorb_true_l at 1. rewrite negb_involutive. revert n1 H.
    apply (nat_2_ind (fun n => check_is_even n = true
                               -> check_is_even (n + n2) = check_is_even n2)).
    + rewrite Nat.add_0_l. reflexivity.
    + intro H. simpl in H. discriminate.
    + intros n1 IHn1 H. apply (IHn1 H).
  - rewrite xorb_false_l. revert n1 H.
    apply (nat_2_ind
             (fun n => check_is_even n = false
                       -> check_is_even (n + n2) = negb (check_is_even n2))).
    + intro H. simpl in H. discriminate.
    + rewrite Nat.add_1_l at 1.
      intro H. clear H. induction n2.
      * reflexivity.
      * apply (f_equal negb) in IHn2. rewrite IHn2.
        symmetry. apply negb_involutive.
    + intros n1 IHn1 H. apply (IHn1 H).
Qed.

Lemma check_is_even_prod (n1 n2 : nat) :
  check_is_even (n1 * n2) = check_is_even n1 || check_is_even n2.
Proof.
  case_eq (check_is_even n1); intro.
  - rewrite orb_true_l. revert n1 H.
    apply (nat_2_ind (fun n => check_is_even n = true
                               -> check_is_even (n * n2) = true)).
    + rewrite Nat.mul_0_l. reflexivity.
    + intro H. simpl in H. discriminate.
    + intros n1 IHn1 H. rewrite <- (IHn1 H). simpl. remember (n1 * n2) as n.
      rewrite Nat.add_assoc. rewrite check_is_even_sum.
      cut (check_is_even (n2 + n2) = true).
      * intro H0. rewrite H0. rewrite xorb_true_l at 1. apply negb_involutive.
      * clear n1 n IHn1 Heqn H. induction n2.
        -- reflexivity.
        -- rewrite Nat.add_succ_r. assumption.
  - rewrite orb_false_l. revert n1 H.
    apply (nat_2_ind (fun n => check_is_even n = false
                               -> check_is_even (n * n2) = check_is_even n2)).
    + intro H. simpl in H. discriminate.
    + rewrite Nat.mul_1_l. reflexivity.
    + intros n1 IHn1 H. rewrite <- (IHn1 H). simpl. remember (n1 * n2) as n.
      rewrite Nat.add_assoc. rewrite check_is_even_sum.
      cut (check_is_even (n2 + n2) = true).
      * intro H0. rewrite H0. rewrite xorb_true_l at 1. apply negb_involutive.
      * clear n1 n IHn1 Heqn H. induction n2.
        -- reflexivity.
        -- rewrite Nat.add_succ_r. assumption.
Qed.

Inductive expr :=
| NatO : expr
| NatS (x : expr) : expr
| NatMul (x y : expr) : expr.

Fixpoint interp (t : expr) : nat :=
  match t with
  | NatO => O
  | NatS x => S (interp x)
  | NatMul x y => interp x * interp y
  end.

Fixpoint check_is_even_expr (t : expr) : bool :=
  match t with
  | NatO => true
  | NatS x => negb (check_is_even_expr x)
  | NatMul x y => orb (check_is_even_expr x) (check_is_even_expr y)
  end.

Lemma check_is_even_equiv (e : expr) :
  check_is_even_expr e = check_is_even (interp e).
Proof.
  induction e.
  - reflexivity.
  - cbn. rewrite IHe. remember (interp e) as n.
    clear e IHe Heqn. induction n.
    + reflexivity.
    + cbn. apply (f_equal negb) in IHn. rewrite <- IHn. apply negb_involutive.
  - cbn. rewrite IHe1, IHe2.
    remember (interp e1) as n1. remember (interp e2) as n2.
    symmetry. apply check_is_even_prod.
Qed.

Theorem check_is_even_expr_sound (e : expr) :
  check_is_even_expr e = true -> is_even (interp e).
Proof.
  rewrite check_is_even_equiv. apply soundness.
Qed.

Ltac reify term :=
  lazymatch term with
  | O => NatO
  | S ?x => let rx := reify x in constr:(NatS rx)
  | ?x * ?y => let rx := reify x in
               let ry := reify y in
               constr:(NatMul rx ry)
  end.

Goal is_even (10*10*10*10*10*10*10*10*10).
  match goal with
  | [ |- is_even ?v ]
    => let e := reify v in
       refine (check_is_even_expr_sound e _)
  end.
  vm_compute. reflexivity.
Qed.
