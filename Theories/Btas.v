(** * Semantic domain of Schedule Algebra *)

From Coq.Arith  Require Import EqNat.
From Coq.Sets   Require Import Ensembles Image.
From Containers Require Import Maps.

Require Export List.
Import ListNotations.

Require Import Omega.

Require Import Actions.

Generalizable All Variables.

(** *)
(** * Bounded-Time Actions *)
(** *)

(** Definition of a bounded-time action. It consits of the action [act], its duration, and the time of its start *)
Record Bta : Type :=
  mk_Bta { act : Action; dur : nat; stt : nat }.

Lemma Bta_eq_dec : forall x y:Bta, {x = y}+{x <> y}.
Proof.
  decide equality.
  apply eq_nat_dec.
  apply eq_nat_dec.
  auto with typeclass_instances.
  apply Action_eq_dec.
Qed.

Definition Bta_lt (a1 a2 : Bta) : Prop :=
  match @_cmp Action _ (act a1) (act a2) with
  | Lt => True
  | Eq => match @_cmp nat _ (dur a1) (dur a2) with
         | Lt => True
         | Eq => match @_cmp nat _ (stt a1) (stt a2) with
                | Lt => True
                | _  => False
                end
         | Gt => False
         end
  | Gt => False
  end.

Definition Bta_gt (a1 a2 : Bta) : Prop :=
  match @_cmp Action _ (act a1) (act a2) with
  | Gt => True
  | Eq => match @_cmp nat _ (dur a1) (dur a2) with
         | Gt => True
         | Eq => match @_cmp nat _ (stt a1) (stt a2) with
                | Gt => True
                | _  => False
                end
         | Lt => False
         end
  | Lt => False
  end.

Lemma _cmp_gen_not_eq : forall A:Type, forall H: OrderedType A, forall a b:A, ~(@_cmp A _ a b = Eq) -> _cmp a b = Lt \/ _cmp a b = Gt.
Proof.
  intros.
  case_eq(_cmp a b);intros.
  contradiction.
  left;auto. right;auto.
Qed.

Lemma _cmp_gen_lt : forall A:Type, forall H: OrderedType A, forall a b:A, @_cmp A _ a b = Lt -> _cmp b a = Gt.
Proof.
  intros.
  apply compare_1 in H0.
  apply elim_compare_gt.
  assumption.
Qed.

Lemma _cmp_gen_gt : forall A:Type, forall H: OrderedType A, forall a b:A, @_cmp A _ a b = Gt -> _cmp b a = Lt.
Proof.
  intros.
  apply compare_3 in H0.
  apply elim_compare_lt.
  order.
Qed.

Lemma Bta_lt_eq_dec : forall a1 a2, {Bta_lt a1 a2}+{~Bta_lt a1 a2}.
Proof.
  intros.
  destruct a1. unfold Bta_lt. simpl.
  destruct a2. simpl; auto.
  case_eq (Action_cmp act0 act1);intros;auto.
  case_eq (OrderedTypeEx.nat_compare dur0 dur1);intros;auto.
  case_eq (OrderedTypeEx.nat_compare stt0 stt1);intros;auto.
Qed.

Lemma Bta_gt_eq_dec : forall a1 a2, {Bta_gt a1 a2}+{~Bta_gt a1 a2}.
Proof.
  intros.
  destruct a1. unfold Bta_gt. simpl.
  destruct a2. simpl; auto.
  case_eq (Action_cmp act0 act1);intros;auto.
  case_eq (OrderedTypeEx.nat_compare dur0 dur1);intros;auto.
  case_eq (OrderedTypeEx.nat_compare stt0 stt1);intros;auto.
Qed.  

Lemma Bta_gt_imp_lt: forall x y, Bta_gt x y -> Bta_lt y x.
Proof.
  intros.
  unfold Bta_lt. unfold Bta_gt in H.
  case_eq (_cmp (act x) (act y)).
  + { intros.
      assert(_cmp (act y) (act x) = Eq) by
          (apply compare_2 in H0; apply elim_compare_eq; auto).
      rewrite H0 in H.
      rewrite H1.
      case_eq (_cmp (dur x) (dur y)).
      - { intro.
          assert(_cmp (dur y) (dur x) = Eq) by
              (apply compare_2 in H2; apply elim_compare_eq; auto).
          rewrite H2 in H.
          rewrite H3.
          case_eq (_cmp (stt x) (stt y)).
          * intro.
            assert(_cmp (stt y) (stt x) = Eq) by
        (apply compare_2 in H4; apply elim_compare_eq; auto).
            rewrite H4 in H.
            rewrite H5.
            trivial.
          * intro.
            rewrite H4 in H. elim H.
          * intro. apply _cmp_gen_gt in H4. rewrite H4. trivial.
        }
      - intro. rewrite H2 in H. elim H.
      - intro. apply _cmp_gen_gt in H2. rewrite H2. trivial.
    }
  + intros. rewrite H0 in H. elim H.
  + intros. apply _cmp_gen_gt in H0. rewrite H0. trivial.
Qed.

Lemma Bta_lt_imp_gt : forall x y, Bta_lt x y -> Bta_gt y x.
Proof.
  intros.
  red in H. red.
  case_eq (_cmp (act x) (act y)).
  + { intros.
      assert(_cmp (act y) (act x) = Eq) by
          (apply compare_2 in H0; apply elim_compare_eq; auto).
      rewrite H0 in H.
      rewrite H1.
      case_eq (_cmp (dur x) (dur y)).
      - { intro.
          assert(_cmp (dur y) (dur x) = Eq) by
              (apply compare_2 in H2; apply elim_compare_eq; auto).
          rewrite H2 in H.
          rewrite H3.
          case_eq (_cmp (stt x) (stt y)).
          * intro.
            assert(_cmp (stt y) (stt x) = Eq) by
        (apply compare_2 in H4; apply elim_compare_eq; auto).
            rewrite H4 in H.
            rewrite H5.
            trivial.
          * intro. apply _cmp_gen_lt in H4. rewrite H4. trivial.
          * intro. rewrite H4 in H. elim H. 
        }
      - intro. apply _cmp_gen_lt in H2. rewrite H2. trivial.
      - intro. rewrite H2 in H. elim H. 
    }
  + intros. apply _cmp_gen_lt in H0. rewrite H0. trivial.
  + intros. rewrite H0 in H. elim H.
Qed.


Definition Bta_Lt (a1 a2:Bta) : Prop :=  
  Action_lt (act a1) (act a2) \/
  (act a1 = act a2 /\ dur a1 < dur a2) \/
  (act a1 = act a2 /\ dur a1 = dur a2 /\ stt a1 < stt a2).


Lemma Bta_lt_imp_Bta_Lt:
  forall x y, Bta_lt x y -> Bta_Lt x y.
Proof.
  intros.
  unfold Bta_lt in H.
  case_eq(_cmp (act x) (act y));intros.
  + { case_eq(_cmp (dur x) (dur y));intros.
      - case_eq(_cmp (stt x) (stt y));intros.
        * rewrite H0, H1, H2 in H. elim H.
        * red. right. right.
          split. apply compare_2 in H0. red in H0. simpl in H0.
          inversion_clear H0;auto.
          split; apply compare_2 in H1. auto.
          apply compare_1 in H2. auto.
        * rewrite H0, H1, H2 in H. elim H.
      - right. left. split.
        * apply compare_2 in H0.
          inversion_clear H0;auto.
        * apply compare_1 in H1. assumption.
      -  rewrite H0, H1 in H. elim H.
    }
  + left.
    case_eq(act x);case_eq(act y);intros.
    subst. rewrite H1, H2 in H0. simpl in H0. discriminate.
    simpl. apply compare_1 in H0. rewrite H1, H2 in H0.  auto. 
    rewrite H1, H2 in H0. simpl in H0. discriminate.
    rewrite H1, H2 in H0.
    simpl in H0.
    constructor.
    apply nat_compare_lt in H0. assumption.
  + rewrite H0 in H.
    elim H.
Qed.

Lemma Bta_Lt_imp_Bta_lt:
  forall x y, Bta_Lt x y -> Bta_lt x y.
Proof.
  intros.
  unfold Bta_Lt in H.
  destruct H as [H1|[H1|H2]].
  + assert(act x <<< act y).
    auto.
    generalize(@elim_compare_lt _ _ (act x) (act y) H);intro.
    unfold Bta_lt.
    assert(_cmp (act x) (act y) = Lt).
    unfold _cmp. simpl. assumption.
    rewrite H2. auto.
  + unfold Bta_lt.
    destruct H1.
    assert(_cmp (act x) (act y) = Eq).
    apply elim_compare_eq. red. rewrite H. auto.
    rewrite H1.
    assert(_cmp (dur x) (dur y) = Lt).
    unfold _cmp. simpl.
    apply nat_compare_lt in H0.
    auto.
    rewrite H2. auto.
  + destruct H2 as [H [H1 H2]].
    assert(_cmp (act x) (act y) = Eq).
    apply elim_compare_eq. auto.
    assert(_cmp (dur x) (dur y) = Eq).
    apply elim_compare_eq. rewrite H1;reflexivity.
    rewrite H. reflexivity.
    unfold Bta_lt.
    rewrite H0,H1.
    assert(_cmp (stt x) (stt y) = Lt).
    apply elim_compare_lt. auto.
    assert(_cmp (dur y) (dur y) = Eq).
    apply elim_compare_eq. reflexivity.
    rewrite H4, H3. trivial.
Qed.

Definition Bta_Gt (a1 a2 : Bta) : Prop :=
  Action_gt (act a1) (act a2) \/
  (act a1 = act a2 /\ dur a1 > dur a2) \/
  ((act a1 = act a2 /\ dur a1 = dur a2) /\ stt a1 > stt a2).

Lemma Bta_gt_imp_Bta_Gt:
  forall x y, Bta_gt x y -> Bta_Gt x y.
Proof.
  intros.
  unfold Bta_gt in H.
  case_eq(_cmp (act x) (act y));intros.
  + { case_eq(_cmp (dur x) (dur y));intros.
      - case_eq(_cmp (stt x) (stt y));intros.
        * rewrite H0, H1, H2 in H. elim H.
        * rewrite H0, H1, H2 in H. elim H.
        * red. right. right.
          split. split.  apply compare_2 in H0. inversion_clear H0.
          reflexivity.
          f_equal. auto.
          apply compare_2 in H1. auto.
          apply compare_3 in H2. auto.
      - rewrite H0, H1 in H. elim H.
      - right. left. split.
        * apply compare_2 in H0.
          inversion_clear H0;auto.
        * apply compare_3 in H1. assumption.
    }
  + rewrite H0 in H. elim H.
  + left.
    apply Action_lt_imp_gt.
    apply compare_3 in H0.
    order.
Qed.

Lemma Bta_Gt_imp_Bta_gt:
  forall x y, Bta_Gt x y -> Bta_gt x y.
Proof.
  intros.
  unfold Bta_Gt in H.
  destruct H as [H1|[H2|H3]].
  + assert(act x >>> act y).
    apply Action_gt_imp_lt in H1.
    auto.
    generalize(@elim_compare_gt _ _ (act x) (act y) H);intro.
    unfold Bta_gt.
    assert(_cmp (act x) (act y) = Gt).
    unfold _cmp. simpl. assumption.
    rewrite H2. auto.
  + unfold Bta_gt.
    destruct H2.
    assert(_cmp (act x) (act y) = Eq).
    apply elim_compare_eq. rewrite H. reflexivity. 
    rewrite H1.
    assert(_cmp (dur x) (dur y) = Gt).
    unfold _cmp. simpl.
    apply nat_compare_gt in H0.
    auto.
    rewrite H2. auto.
  + destruct H3. destruct H. 
    assert(_cmp (act x) (act y) = Eq).
    apply elim_compare_eq. rewrite H;auto.
    assert(_cmp (dur x) (dur y) = Eq).
    apply elim_compare_eq. auto.
    unfold Bta_gt.
    rewrite H2,H3.
    assert(_cmp (stt x) (stt y) = Gt).
    unfold _cmp. simpl.
    apply nat_compare_gt in H0.
    auto.
    rewrite H4.
    auto.
Qed.

Instance Bta_Gt_Trans: Transitive Bta_Lt.
Proof.
  red.
  intros.
  destruct H.
  + { destruct H0.
      - red.
        left.
        etransitivity;eauto.
      - destruct H0.
        destruct H0.
        unfold Bta_Lt.
        left. rewrite H0 in H. auto.
        destruct H0.  rewrite H0 in H.
        unfold Bta_Lt. left. auto.
    }
  + { destruct H.
      - destruct H.
        destruct H0.
        * unfold Bta_Lt. left. rewrite H. auto.
        * { destruct H0.
            destruct H0.
            unfold Bta_Lt.
            right. left.
            split;(etransitivity;eauto).
            destruct H0 as [H2 [H3 H4]].
            unfold Bta_Lt.
            right. left. rewrite H. rewrite H3 in H1. auto.
          }
      - destruct H as [H1 [H2 H3]].
        destruct H0.
        * left. rewrite H1. auto.
        * { destruct H.
            destruct H.
            right. left. split.
            etransitivity;eauto.
            rewrite H2. auto.
            destruct H.
            destruct H0.
            right. right.
            split.
            etransitivity;eauto.
            split.
            etransitivity;eauto.
            etransitivity;eauto.
          }
    }
Qed.

Lemma Bta_not_lt_gt :
  forall x y, ~(Bta_gt x y /\ Bta_lt x y).
Proof.
  intros.
  intro.
  destruct H.
  apply Bta_gt_imp_lt in H.
  red in H,H0.
  case_eq(_cmp (act x) (act y)).
  + { intro.
      rewrite H1 in H0.
      assert(_cmp (act y) (act x) = Eq) by
          (apply compare_2 in H1; apply elim_compare_eq; auto).
      rewrite H2 in H.
      case_eq (_cmp (dur x) (dur y)).
      - { intro.
          assert(_cmp (dur y) (dur x) = Eq) by
              (apply compare_2 in H3; apply elim_compare_eq; auto).
          rewrite H3 in H0.
          rewrite H4 in H.
          case_eq (_cmp (stt x) (stt y)).
          * intro.
            assert(_cmp (stt y) (stt x) = Eq) by
        (apply compare_2 in H5; apply elim_compare_eq; auto).
            rewrite H5 in H0.
            elim H0.
          * intro.
            apply _cmp_gen_lt in H5.
            rewrite H5 in H.
            elim H.
          * intros.
            rewrite H5 in H0. elim H0.
        }
      - intros.
        apply _cmp_gen_lt in H3.
        rewrite H3 in H. elim H.
      - intros. rewrite H3 in H0. elim H0.
    }
  + intro. apply _cmp_gen_lt in H1. rewrite H1 in H. elim H.
  + intro. rewrite H1 in H0. elim H0.
Qed.

Lemma Bta_not_gt_eq :
  forall x y, ~(Bta_gt x y /\ x = y).
Proof.
  intros.
  intro.
  destruct H.
  unfold Bta_gt in H.
  assert(_cmp (act x) (act y) = Eq).
  rewrite H0.
  apply elim_compare_eq. reflexivity.
  assert(_cmp (dur x) (dur y) = Eq).
  rewrite H0. apply elim_compare_eq. reflexivity.
  assert(_cmp (stt x) (stt y) = Eq).
  rewrite H0. apply elim_compare_eq. reflexivity.
  rewrite H1, H2, H3 in H. elim H.
Qed.

Lemma Bta_not_lt_eq :
  forall x y, ~(Bta_lt x y /\ x = y).
Proof.
  intros.
  intro.
  destruct H.
  unfold Bta_lt in H.
  assert(_cmp (act x) (act y) = Eq).
  rewrite H0.
  apply elim_compare_eq. reflexivity.
  assert(_cmp (dur x) (dur y) = Eq).
  rewrite H0. apply elim_compare_eq. reflexivity.
  assert(_cmp (stt x) (stt y) = Eq).
  rewrite H0. apply elim_compare_eq. reflexivity.
  rewrite H1, H2, H3 in H. elim H.
Qed.


Lemma Bta_lt_not_imp : forall x y, ~Bta_lt x y -> x = y \/ Bta_gt x y.
Proof.
  intros.
  unfold Bta_lt in H.
  unfold Bta_gt.
  case_eq(_cmp (act x) (act y)).
  + { intro.
      rewrite H0 in H.
      case_eq(_cmp (dur x) (dur y)).
      - { intro. rewrite H1 in H.
          case_eq(_cmp (stt x) (stt y)).
          * intro.
            apply compare_2 in H0. red in H0. red in H0. simpl in H0 .
            apply compare_2 in H1. red in H1. red in H1. simpl in H1 . 
            apply compare_2 in H2. red in H2. red in H2. simpl in H2 .
            destruct x. destruct y.
            simpl in *. apply Action_eq_impl_eq in H0. 
            rewrite H0. rewrite H1. rewrite H2. auto.
          * intro.
            rewrite H2 in H. auto.
          * intro. auto.
        }
      - intro. rewrite H1 in H. auto.
      - intro. auto.
    }
  + intro. rewrite H0 in H. auto.
  + intro. auto.
Qed.

Instance Bta_lt_trans : Transitive Bta_lt.
Proof.
  unfold Transitive.
  intros.
  apply Bta_lt_imp_Bta_Lt in H.
  apply Bta_lt_imp_Bta_Lt in H0.
  apply Bta_Lt_imp_Bta_lt.
  etransitivity;eauto.
Qed.

Instance Bta_lt_SO : OrderedType.StrictOrder Bta_lt eq.
Proof.
  constructor.
  auto with typeclass_instances.
  intros.
  intro.
  pose proof (Bta_not_lt_eq x y).
  apply H1;split;auto.
Qed.

Definition Bta_cmp (a1 a2 : Bta) : comparison :=
  match Bta_eq_dec a1 a2 with
  | left _ => Eq
  | right _ => match Bta_lt_eq_dec a1 a2 with
              | left _ => Lt
              | right _ => Gt
              end
  end.

Lemma Bta_cmp_spec:
  forall x y : Bta, compare_spec eq Bta_lt x y (Bta_cmp x y).
Proof.
  intros.
  case_eq(Bta_cmp x y);intro.
  constructor.
    unfold Bta_cmp in H.
  case_eq(Bta_eq_dec x y);intros.
  assumption.
  rewrite H0 in H.
  destruct(Bta_lt_eq_dec x y);discriminate.
  constructor.
  unfold Bta_cmp in H.
  case_eq(Bta_eq_dec x y);intros.
  rewrite H0 in H.
  discriminate.
  rewrite H0 in H.
  destruct(Bta_lt_eq_dec x y).
  assumption.
  discriminate.
  unfold Bta_cmp in H.
  case_eq(Bta_eq_dec x y);intros.
  rewrite H0 in H.
  discriminate.
  rewrite H0 in H.
  destruct(Bta_lt_eq_dec x y).
  discriminate.
  pose proof (Bta_lt_not_imp x y n0).
  destruct H1. contradiction.
  constructor.
  apply Bta_gt_imp_lt in H1. assumption.
Qed.

Instance Bta_Ordered: OrderedType Bta :=
  {|
    _eq := @eq Bta ;
    _lt := Bta_lt ;
    _cmp := Bta_cmp
  |}.
Proof. apply Bta_cmp_spec. Defined.

Definition Bta_off (a:Bta)(t:nat) : Bta :=
  mk_Bta (act a) (dur a) (stt a + t).




