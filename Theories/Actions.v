From Coq.Classes Require Export Morphisms Equivalence.
From Coq.Setoids Require Export Setoid.
From Coq.Arith   Require Import PeanoNat.

From Containers Require Export OrderedType OrderedTypeEx Generate.

Require Import Omega.


(** *)
(** * Definition of an atomic action. *)
(** An atomic action is a member of the inductive type [Action], and can have two forms: *)
(** *)

Inductive Action : Type :=
(** Empty action *)
| noAct : Action
(** Some action *)
| aAct  : nat -> Action.

(** Use [Containers] facilities to generate the constructs and proofs that [Action] is an ordered type (with custom equality). *)

Generate OrderedType Action.

Lemma Action_lt_neq : forall x y : Action, Action_lt x y -> x =/= y.
Proof.
  intros.
  inversion_clear H. intro. red in H. simpl in H.
  inversion H.
  intro.
  inversion H. order.
Qed.

Instance Action_lt_SO : StrictOrder Action_lt eq.
Proof.
  constructor.
  - auto with typeclass_instances.
  - intros. normalize_notations. intro. rewrite H0 in H.  order.
Qed.

Lemma Action_cmp_spec : forall x y : Action, compare_spec eq Action_lt x y (Action_cmp x y).
Proof.
  induction x;intros.
  - destruct y.
    + constructor;auto.
    + constructor. constructor. 
  - destruct y.
    + constructor.  constructor. 
    + simpl. case_eq(compare n n0);intros.
      * constructor. apply nat_compare_eq in H. subst;auto.
      * constructor. apply nat_compare_Lt_lt in H. constructor.  order. 
      * constructor. apply nat_compare_Gt_gt in H. constructor.  order.
Qed. 

Instance Action_OT : UsualOrderedType Action :=
  {|
    SOT_lt  := Action_lt;
    SOT_cmp := Action_cmp
  |}.
Proof.
  apply Action_cmp_spec.
Defined.

Lemma Action_eq_dec : forall x y:Action, {x=y}+{x<>y}.
Proof.
  intros.
  decide equality.
  apply eq_nat_dec.
Qed.

Definition Action_gt (a1 a2:Action) : Prop :=
  match a1 with
  | noAct => match a2 with
            | noAct => False
            | _     => False
            end
  | aAct a => match a2 with
             | noAct  => True
             | aAct b => a > b
             end
  end.

Lemma Action_gt_imp_lt : forall x y, Action_gt x y -> Action_lt y x.
Proof.
  destruct x.
  - intros. unfold Action_gt in H. destruct y. elim H. elim H.
  - intros. unfold Action_gt in H. destruct y. constructor. constructor. 
    order. 
Qed.

Lemma Action_lt_imp_gt : forall x y, Action_lt x y -> Action_gt y x.
Proof.
  induction 1.
  - simpl. auto.
  - simpl. order.
Qed.

Lemma Action_eq_impl_eq : forall x y, Action_eq x y -> x = y.
Proof.
  induction 1;auto.
Qed.




