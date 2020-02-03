Require Export Actions.


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
