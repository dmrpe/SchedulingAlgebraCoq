(** * Semantic domain of Schedule Algebra *)

From Coq.Arith Require Import EqNat.
From Coq.Sets  Require Import Ensembles Image.

Require Export List.
Import ListNotations.

Require Import Omega.

Generalizable All Variables.

Section Semantic_Model.

  Context {Act:Type}.
  Context {eqAct : Act -> Act -> Prop}.
  Context {eqAct_dec : (forall x y : Act, {eqAct x y} + {~ eqAct x y})}.

  (** *)
  (** * Action as a triple with duration and start time *)
  (** *)
  
  Record ActEx : Type :=
    mk_ActEx { act : Act; duration : nat; start : nat }.

  Definition ActEx_eq : ActEx -> ActEx -> Prop :=
    fun x y =>
      eqAct (act x) (act y) /\ (duration x) = duration y /\ start x = start y.
                                                                            
  Corollary ActEx_dec : forall x y : ActEx, {ActEx_eq x y} + {~ ActEx_eq x y}.
  Proof.
    intros.
    unfold ActEx_eq.
    destruct (eqAct_dec (act x) (act y));
    destruct(eq_nat_decide (duration x) (duration y)) as [e0|e0];
    destruct(eq_nat_decide (start x) (start y)) as [e1|e1];
    try (apply eq_nat_eq in e0); try (apply eq_nat_eq in e1);intuition.
  Qed.

  Definition ActEx_offset (a:ActEx)(t:nat) : ActEx :=
    mk_ActEx (act a) (duration a) ((start a) + t).

  (** *)
  (** * Multisets of action triplets as lists *)
  (** To replace in the future by a better model. *)
  (** *)
  
  Definition MS_ActEx := list ActEx.
  
  Definition Emp_MS_ActEx : MS_ActEx := [].

  Definition Singleton_MS_ActEx (a:Act) (d s:nat) : MS_ActEx := 
    [mk_ActEx a d s].

  Definition Union_MS_ActEx (a b:MS_ActEx) : MS_ActEx := a ++ b.

  Definition Offset_MS_ActEx (s:MS_ActEx) (t:nat) : MS_ActEx :=
    map ((fun x:ActEx => ActEx_offset x t)) s.

  (** *)
  (** * The semantic model of schedule algebra *)
  (** Need to find a more suited name. *)
  
  Record Atom : Type :=
    mk_Atom {
        actions       : MS_ActEx;
        st_fin_times  : Ensemble nat;
        anchors       : Ensemble nat;
        anchors_not_0 : forall n:nat, Ensembles.In nat anchors n -> n <> 0
      }.

  Lemma anchors_not_0_union :
    forall a b : Atom, forall n : nat,
        Ensembles.In nat (Union nat (anchors a) (anchors b)) n -> n <> 0.
  Proof.
    intros; inversion_clear H; [ destruct a | destruct b]; simpl in *;
      (apply anchors_not_1; exact H0).
  Qed.

  Definition AtomUnion (a b:Atom) : Atom :=
    mk_Atom (Union_MS_ActEx (actions a) (actions b))
            (Union _ (st_fin_times a) (st_fin_times b))
            (Union _ (anchors a) (anchors b))
            (anchors_not_0_union a b).

  Definition Atom_Offset_Map (a:Atom)(t:nat) : Atom.
  Proof.
    refine(mk_Atom (Offset_MS_ActEx (actions a) t)
                   (Im _ _ (st_fin_times a) (fun x:nat => x + t))
                   (Im _ _ (anchors a) (fun x:nat => x + t))
                   _).
    abstract(intros; destruct a; simpl in *; eapply Im_inv in H;
      destruct H as [x Hx]; destruct Hx; rewrite <- H0;
        apply anchors_not_1 in H;
        omega).
  Defined.

  Lemma Empty_not_in_0 :  forall n : nat, Ensembles.In nat (Empty_set nat) n -> n <> 0.
  Proof.
    intros;inversion H.
  Qed.
  
  Definition At := Ensemble Atom. 

  (** An empty schedule atom. *)
  Definition empty_atom : At :=
    Singleton Atom
              (mk_Atom Emp_MS_ActEx (Singleton _ 0) (Empty_set nat) (Empty_not_in_0)).

  (** A single action scheduling atom. *)
  Definition act_atom (a:Act)(t:nat) : At :=
    Singleton Atom
              (mk_Atom (Singleton_MS_ActEx a t 0) (Singleton _ 0) (Empty_set nat) (Empty_not_in_0)).

  Lemma Sequence_Atom (t:nat) :
    forall n : nat,
      Ensembles.In nat (Setminus nat (Singleton nat t) (Singleton nat 0)) n -> n <> 0.
  Proof.
    intros n H;inversion H;intro H2;apply H1;
      rewrite H2;constructor.
  Qed.

  (** Sequence of actions, prefixed by a timed action atom. *)
  Definition seq_atom (a:Act)(t:nat)(P:Atom) : At := 
    Singleton Atom ( 
                AtomUnion (mk_Atom (Singleton_MS_ActEx a t 0)
                                   (Singleton _ 0)
                                   (Setminus nat (Singleton nat t) (Singleton nat 0))
                                   (Sequence_Atom t))
                          (Atom_Offset_Map P t)).


  Definition offset_atom (t:nat)(P:Atom) : At :=
    Singleton Atom (
                AtomUnion (mk_Atom Emp_MS_ActEx
                                   (Singleton _ 0)
                                   (Setminus nat (Singleton nat t) (Singleton nat 0))
                                   (Sequence_Atom t))
                          (Atom_Offset_Map P t)).
  
  Inductive Delay_Atom (P:Atom) : At :=
  | delay_atom: forall t:nat,
      Ensembles.In _ (Delay_Atom P) (AtomUnion (mk_Atom Emp_MS_ActEx
                                              (Singleton _ 0)
                                              (Empty_set nat)
                                              Empty_not_in_0)
                                               (Atom_Offset_Map P t)).

  Inductive Elim_Delay_Atom (P:At) : At :=
  | elim_delay_atom :
      forall a, Ensembles.In _ P a -> Strict_Included _ (st_fin_times a) (anchors a) ->
           Ensembles.In _ (Elim_Delay_Atom P) a.

  Definition union_atom (a b:At) : At :=
    Union Atom a b.

  
                                      

  
  
