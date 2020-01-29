(** *)
(** * The concept of schedule *)
(** *)

Record Schedule : Type :=
  mk_Sched {
      actions       : MS_ActEx;
      st_fin_times  : Ensemble nat;
      anchors       : Ensemble nat;
      anchors_not_0 : forall n:nat, Ensembles.In nat anchors n -> n <> 0
    }.

Notation "⟨ x ';' y ';' z ⟩" := (fun t => mk_Sched x y z t)(at level 10, no associativity).

Lemma Schedule_anchors_not_0_union :
  forall a b : Schedule, forall n : nat,
      Ensembles.In nat (Union nat (anchors a) (anchors b)) n -> n <> 0.
Proof.
  intros; inversion_clear H; [ destruct a | destruct b]; simpl in *;
    (apply anchors_not_1; exact H0).
Qed.

Definition Schedule_Union (a b:Schedule) : Schedule :=
  ⟨ Union_MS_ActEx (actions a) (actions b) ;
    Union _ (st_fin_times a) (st_fin_times b) ;
    Union _ (anchors a) (anchors b) ⟩ (Schedule_anchors_not_0_union a b).


Definition Atom_Offset_Map (a:Schedule)(t:nat) : Schedule.
Proof.
  refine(⟨ Offset_MS_ActEx (actions a) t ;
           Im _ _ (st_fin_times a) (fun x:nat => x + t) ;
           Im _ _ (anchors a) (fun x:nat => x + t) ⟩ _).
  abstract(intros; destruct a; simpl in *; eapply Im_inv in H;
           destruct H as [x Hx]; destruct Hx; rewrite <- H0;
           apply anchors_not_1 in H;
           omega).
Defined.

Lemma Empty_not_in_0 :  forall n : nat, Ensembles.In nat (Empty_set nat) n -> n <> 0.
Proof. intros;inversion H. Qed.

(** *)
(** * Semantic model for the interpretation of schedule specifications *)
(** *)
(** Schedule specifications are interpreted as sets of [Schedule] types. *)
(** *)
  
Definition Schedules := Ensemble Schedule. 

(** An empty schedule atom. *)
Definition empty_Schedule : Schedules :=
  Singleton Schedule
            (⟨ Emp_MS_ActEx ; (Singleton _ 0) ; (Empty_set nat) ⟩ Empty_not_in_0).

(** A single action scheduling atom. *)
Definition act_atom (a:Action)(t:nat) : Schedules :=
  Singleton Schedule
            (⟨ Singleton_MS_ActEx a t 0 ; Singleton _ 0 ; Empty_set nat ⟩ Empty_not_in_0).

Lemma Sequence_Atom (t:nat) :
  forall n : nat, Ensembles.In nat (Setminus nat (Singleton nat t) (Singleton nat 0)) n -> n <> 0.
Proof.
  intros n H;inversion H;intro H2;apply H1;
    rewrite H2;constructor.
Qed.

Definition SeqSchedule_act(a:Action)(t:nat) : Schedule :=
  ⟨ Singleton_MS_ActEx a t 0 ;
    Singleton _ 0 ;
    Setminus _ (Singleton _ t) (Singleton _ 0) ⟩ (Sequence_Atom t).


(** Sequence of actions, prefixed by a timed action atom. *)
Inductive Seq_Schedule (a:Action)(t:nat)(P:Schedules) : Schedules :=
| in_seq_act :
    Ensembles.In _ (Seq_Schedule a t P) (SeqSchedule_act a t)
| in_seq_offset : forall s,
    Ensembles.In _ P s -> Ensembles.In _ (Seq_Schedule a t P) (Atom_Offset_Map s t).

Inductive Offset_Schedule (t:nat)(P:Schedules) : Schedules :=
| in_offset_act :
    Ensembles.In _ (Offset_Schedule t P)
                 (⟨Emp_MS_ActEx ; Singleton _ 0 ; Setminus nat (Singleton nat t) (Singleton nat 0)⟩
                    (Sequence_Atom t))
| in_offset_seq : forall s,
    Ensembles.In _ P s -> Ensembles.In _ (Offset_Schedule t P) (Atom_Offset_Map s t).

Inductive Delay_Atom (P:Atom) : At :=
| delay_atom: forall t:nat,
    Ensembles.In
      _
      (Delay_Atom P)
      ⟨ Emp_MS_ActEx ; Singleton _ 0 ; Setminus nat (Singleton nat t) (Singleton nat 0) ⟩ 

Definition offset_atom (t:nat)(P:Atom) : At :=
  Singleton Atom (
              AtomUnion (mk_Atom Emp_MS_ActEx
                                 (Singleton _ 0)
                                 (Setminus nat (Singleton nat t) (Singleton nat 0))
                                 (Sequence_Atom t))
                        (Atom_Offset_Map P t)).
⟩


                 (AtomUnion (mk_Atom Emp_MS_ActEx
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

  
                                      

  
  
