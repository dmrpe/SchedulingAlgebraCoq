From Containers Require Import Maps MapFacts.
Require Import Arith.

Record Multiset (A:Type) {H:OrderedType A} : Type :=
  {
    ms :> Map[A,nat];
    ms_safe : forall x n, find x ms = Some n -> n >= 1
  }.


Definition null (A:Type) {H:OrderedType A} (m:Multiset A) : bool :=
  is_empty (ms _ m).

Definition mempty (A:Type) {H:OrderedType A} : Multiset A.
  refine(Build_Multiset A _ (@empty A H _ nat) _).
  abstract(intros;vm_compute in H0;discriminate).
Defined.

Lemma null_correct : forall (A:Type) {H:OrderedType A}, null A (mempty A) = true.
Proof.
  intros.
  unfold null. simpl. vm_compute. reflexivity.
Qed.

Check @add.

Lemma msingleton_aux:
  forall (A : Type) (H:OrderedType A) (x : A),
  forall (x0 : A) (n : nat), (([]) [x <- 1]) [x0] = Some n -> n >= 1.
Proof.
  intros.
  destruct(eq_dec x x0);intros.
  + pose proof (@add_eq_o A _ _ _ _ ([]) x x0 1 H1).
    rewrite H2 in H0. injection H0. intros. subst. auto with arith.
  + apply find_mapsto_iff in H0.
    apply add_mapsto_iff in H0.
    destruct H0.
    destruct H0. contradiction.
    destruct H0. apply empty_mapsto_iff in H2. elim H2.
Qed.

Definition msingleton (A:Type) {H:OrderedType A} (x:A) : Multiset A.
  refine(Build_Multiset A _ (@add A H _ nat x 1 (@empty A H _ nat))  _).
  abstract(intros;eapply msingleton_aux;eauto).
Defined.

Definition munion (A:Type) {H:OrderedType A} (m1 m2 : Multiset A) : Multiset A.


Print msingleton.
