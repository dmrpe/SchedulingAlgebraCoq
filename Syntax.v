Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.PeanoNat.

From Containers Require Import OrderedType OrderedTypeEx Maps.

Require Import Omega.

Generalizable All Variables.


Inductive Action : Type :=
(** Empty action *)
| noAct : Action
(** Some action *)
| aAct  : nat -> Action.

Theorem Action_Eq_Inj : forall a b, aAct a = aAct b -> a = b.
Proof.
  intros; inversion H; auto.
Qed.

Theorem Action_Eq_Inj_inv : forall a b, a <> b -> aAct a <> aAct b.
Proof.
  intros. intro. apply Action_Eq_Inj in H0. contradiction.
Qed.

Theorem Action_Eq_Dec : forall x y:Action, {x=y}+{x<>y}.
Proof.
  intros.
  decide equality.
  apply (Nat.eq_dec n n0).
Qed.

Definition Action_lt (a1 a2:Action) : Prop :=
  match a1 with
  | noAct => match a2 with
            | noAct => False
            | _     => True
            end
  | aAct a => match a2 with
             | noAct  => False
             | aAct b => a < b
             end
  end.

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
  - intros. unfold Action_gt in H. destruct y. simpl. auto.
    simpl. omega.
Qed.

Lemma Action_lt_imp_gt : forall x y, Action_lt x y -> Action_gt y x.
Proof.
  destruct x.
  - intros. unfold Action_lt in H. destruct y. elim H. simpl.  auto. 
  - intros. unfold Action_lt in H. destruct y. elim H. simpl. auto.
Qed.

Lemma Action_neg_lt_imp : forall x y, ~Action_lt x y -> Action_gt x y \/ x = y.
Proof.
  destruct x.
  - intros. unfold Action_lt in H. destruct y. auto. elim H. auto.
  - intros. unfold Action_lt in H. destruct y. simpl. auto.
    simpl. apply Nat.nlt_ge in H.
    apply le_lt_or_eq in H.
    destruct H;auto.
Qed.


Lemma Action_lt_eq_dec : forall a1 a2, {Action_lt a1 a2}+{~Action_lt a1 a2}.
Proof.
  destruct a1.
  - intro. simpl.
    destruct a2; simpl; auto.
  - intro. simpl.
    destruct a2;auto.
    apply lt_dec.
Qed.

Lemma Action_gt_eq_dec : forall a1 a2, {Action_gt a1 a2}+{~Action_gt a1 a2}.
Proof.
  destruct a1.
  - intro. simpl.
    destruct a2; simpl; auto.
  - intro. simpl.
    destruct a2;auto.
    apply lt_dec.
Qed.

Definition Action_cmp (a1 a2 : Action) : comparison :=
  match a1 with
  | noAct => match a2 with
            | noAct => Eq
            | aAct _ => Lt
            end
  | aAct x => match a2 with
             | noAct => Gt
             | aAct y => _cmp x y
             end
  end.

Instance Action_lt_trans : Transitive Action_lt.
Proof.
  repeat red.
  induction x;intros.
  - destruct y.
    + simpl in H. elim H.
    + destruct z.
      * simpl in H0. elim H0.
      * auto.
  - destruct y.
    + simpl in H. elim H.
    + destruct z.
      * auto.
      * simpl in H,H0. etransitivity;eauto.
Qed.

Lemma Action_lt_neq : forall x y : Action, Action_lt x y -> x =/= y.
Proof.
  induction x;intros.
  - destruct y.
    + elim H.
    + intro. discriminate.
  - intro. rewrite <- H0 in H.
    simpl in H. omega.
Qed.
      
Instance Action_lt_SO : StrictOrder Action_lt eq.
Proof.
  constructor.
  - apply Action_lt_trans.
  - apply Action_lt_neq.
Qed.

Lemma Action_cmp_spec : forall x y : Action, compare_spec eq Action_lt x y (Action_cmp x y).
Proof.
  induction x;intros.
  - destruct y.
    + constructor;auto.
    + constructor. simpl. auto.
  - destruct y.
    + constructor. simpl. auto.
    + simpl. case_eq(OrderedTypeEx.nat_compare n n0);intros.
      * constructor. apply nat_compare_eq in H. subst;auto.
      * constructor. apply nat_compare_Lt_lt in H. simpl. assumption.
      * constructor. apply nat_compare_Gt_gt in H. simpl.
        unfold lt.
        unfold gt in H.
        destruct n.
        omega.
        omega.
Qed.

Instance Action_OT : UsualOrderedType Action :=
  {|
    SOT_lt  := Action_lt;
    SOT_cmp := Action_cmp
  |}.
Proof.
  apply Action_cmp_spec.
Defined.

Inductive term : Type :=
(** Empty process (lifting of empty action to processes)  *)
| empProc    : term
(** Execution of a single action during some time *)
| singleProc : Action -> nat -> term
(** Execution of an action during some time, followed by other process(es) *)
| seqProc    : Action -> nat  -> term -> term
(** Offsetting the execution of a process for a given number of time units *)
| offsetProc : nat -> term -> term
(** Unbounded delay of a process *)
| delayProc  : term -> term
(** Elimination of delays *)
| elimProc   : term -> term
(** Non-deterministic choice between two processes *)
| choiceProc : term -> term -> term
(** Concurrent execution of processes *)
| forkProc   : term -> term -> term.

(*Notation "'ϵ'" := (empProc)(at level 0).

Notation "❲ t ❳ x" := (offsetProc  t x)(at level 11, left associativity).
Notation "Δ( t )"  := (delayProc t)(at level 1).
Notation "⟦ x ⟧"   := (elimProc x)(at level 1).

Notation "'⧼' a ',' t '⧽'"   := (singleProc a t)(at level 10).
Notation "a '[' t ']' '⋅' x" := (seqProc a t x)(at level 20, left associativity).

Notation "x '∪' y" := (choiceProc x y)(at level 50, left associativity).
Notation "x '⫙' y" := (forkProc x y)(at level 50, left associativity).

Reserved Notation "x '≃' y" (at level 60, no associativity).

Inductive SA_Eq : term -> term -> Prop :=
| A1 : forall a b c  , a ∪ (b ∪ c) ≃ (a ∪ b) ∪ c
| A2 : forall a b    , a ∪ b ≃ b ∪ a
| A3 : forall a      , a ∪ a ≃ a
| A4 : forall a b c  , a ⫙ (b ⫙ c) ≃ (a ⫙ b) ⫙ c
| A5 : forall a b    , a ⫙ b ≃ b ⫙ a
| Z1 : forall a x    , (a[0] ⋅ x) ≃ x
| Z2 : forall a      , a ⫙ ϵ ≃ a
| D1 : forall t a b  , ❲t❳(a ∪ b) ≃ (❲t❳a) ∪ (❲t❳b)
| D2 : forall a b    , Δ(a ∪ b) ≃ (Δ(a) ∪ Δ(b)) 
| D3 : forall a b c  , (a ⫙ (b ∪ c)) ≃ ((a ⫙ b) ∪ (a ⫙ c))
| N1 : forall a t x  , a[t]⊙ x ≃ (⧼a,t⧽) ⫙ x
| N2 : forall t x u y, (❲t❳x) ⫙ (❲(t+u)❳y) ≃ ❲t❳(x ⫙ (❲u❳y))
| N3 : forall x y    , Δ(x) ⫙ Δ(y) ≃ Δ((x ⫙ Δ(y)) ∪ (y ⫙ Δ(x)))
| AA1: forall a b    , ⟦a ∪ b⟧ ≃ ⟦a⟧ ∪ ⟦b⟧
| AA2: forall a t x  , ⟦⧼a,t⧽ ⫙ x⟧ ≃ ⧼a,t⧽ ∪ ⟦x⟧
| AA3: forall t x    , ⟦❲t❳x⟧ ≃ ❲t❳⟦x⟧
| AA4: forall x      , ⟦Δ(x)⟧ ≃ ⟦x⟧
| AA5: forall t x y  , ⟦❲t❳x ⫙ Δ(y)⟧ ≃ (((❲t❳x) ⫙ Δ(y)) ∪ (❲t❳(x ⫙ Δ(y))))
| AA6: ⟦Δ(ϵ)⟧ ≃ ϵ
| SA_Eq_refl  : forall x, x ≃ x
| SA_Eq_symm  : forall x y, x ≃ y -> y ≃ x
| SA_Eq_trans : forall x y, x ≃ y -> forall z, y ≃ z -> x ≃ z 
where "x '≃' y" := (SA_Eq x y).


Instance SA_Eq_REFL : Reflexive SA_Eq.
Proof. constructor. Qed.

Instance SA_Eq_Symm : Symmetric SA_Eq.
Proof. constructor. exact H. Qed.

Instance SA_Eq_Trans : Transitive SA_Eq.
Proof. econstructor. symmetry. eapply SA_Eq_trans with y;auto. Qed.

Instance SA_Eq_Equiv : Equivalence SA_Eq.
Proof.
  econstructor;eauto. apply SA_Eq_REFL. apply SA_Eq_Symm. apply SA_Eq_Trans.
Qed.
*)
  
