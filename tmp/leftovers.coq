Theorem Action_Eq_Inj : forall a b, aAct a = aAct b -> a = b.
Proof.
  intros; inversion H; auto.
Qed.

Theorem Action_Eq_Inj_inv : forall a b, a <> b -> aAct a <> aAct b.
Proof.
  intros. intro. apply Action_Eq_Inj in H0. contradiction.
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

