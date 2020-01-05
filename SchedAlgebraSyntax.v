Require Import Coq.Classes.Equivalence.
Require Import Coq.Setoids.Setoid.

Generalizable All Variables.


Section TermSyntax_and_Axioms.

  Context {Action:Type}.

  Inductive term  : Type :=
  | EmptyProcess : term
  | StartWithDuration : Action -> nat -> term
  | Sequence : Action -> nat  -> term -> term
  | Offset : nat -> term -> term
  | Delay : term -> term
  | DelayElim : term -> term
  | Choice : term -> term -> term
  | Fork : term -> term -> term.

  Notation "'ϵ'" := EmptyProcess.
  Notation "a '(' t ')+'" := (StartWithDuration a t)(at level 50).
  Notation "a '(' t ')' '·' x" := (Sequence a t x)(at level 51).
  Notation "'Δ(' x ')'" := (Delay x)(at level 52).
  Notation "x '∪' y" := (Choice x y)(at level 53). 
  
  Reserved Notation "x '=sa=' y" (at level 50, only parsing).


  Inductive SA_Eq : term -> term -> Prop :=
  | SA_Eq_refl : forall x, x =sa= x
  | SA_Eq_symm : forall x y, x =sa= y -> y =sa= x
  | SA_Eq_trans : forall x y, x =sa= y -> forall z, y =sa= z -> x =sa= z 
  | A1 : forall a b c, Choice a (Choice b c) =sa= Choice (Choice a b) c
  | A2 : forall a b, Choice a b =sa= Choice b a
  | A3 : forall a, Choice a a =sa= a
  | A4 : forall a b c, Fork a (Fork b c) =sa= Fork (Fork a b) c
  | A5 : forall a b, Fork a b =sa= Fork b a
  | Z1 : forall a x, Sequence a 0 x =sa= x
  | Z2 : forall a, Fork a EmptyProcess =sa= a
  | D1 : forall t a b, Offset t (Choice a b) =sa= Choice (Offset t a) (Offset t b)
  | D2 : forall a b, Delay (Choice a b) =sa= Choice (Delay a) (Delay b)
  | D3 : forall a b c, Fork a (Choice b c) =sa= Choice (Fork a b) (Fork a c)
  | N1 : forall a t x, Sequence a t x =sa= Fork (StartWithDuration a t) x
  | N2 : forall t x u y, Fork (Offset t x) (Offset (t+u) y) =sa= Offset t (Fork x (Offset u y))
  | N3 : forall x y, Fork (Delay x) (Delay y) =sa= Delay (Choice (Fork x (Delay y)) (Fork y (Delay x)))
  | AA1: forall a b, DelayElim (Choice a b) =sa= Choice (DelayElim a) (DelayElim b)
  | AA2: forall a t x, DelayElim (Fork (StartWithDuration a t) x) =sa= Fork (StartWithDuration a t) (DelayElim x)
  | AA3: forall t x, DelayElim (Offset t x) =sa= Offset t (DelayElim x)
  | AA4: forall x, DelayElim (Delay x) =sa= DelayElim x
  | AA5: forall t x y,
      DelayElim (Fork (Offset t x) (Delay y)) =sa= Choice (Fork (Offset t x) (Delay y)) (Offset t (Fork x (Delay y)))
  | AA6: DelayElim (Delay EmptyProcess) =sa= EmptyProcess
  where "x '=sa=' y" := (SA_Eq x y).


  Print SA_Eq.
  

  Instance SA_Eq_REFL : Reflexive SA_Eq.
  constructor.
  Qed.

  Instance SA_Eq_Symm : Symmetric SA_Eq.
  constructor.
  exact H.
  Qed.

  Instance SA_Eq_Trans : Transitive SA_Eq.
  econstructor.
  symmetry.
  eapply SA_Eq_trans with y;auto.
  Qed.

  Instance SA_Eq_Equiv : Equivalence SA_Eq.
  econstructor;eauto.
  apply SA_Eq_REFL.
  apply SA_Eq_Symm.
  apply SA_Eq_Trans.
  Qed.

  Lemma experiment :
    forall a t x y, Sequence a t (Choice x y) =sa= Choice (Sequence a t x) (Sequence a t y).
  Proof.
    intros.
    rewrite N1.
    rewrite D3.
