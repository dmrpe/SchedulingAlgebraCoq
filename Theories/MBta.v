Require Export Actions.
Require Export Btas.

From Containers Require Export Maps.

(** *)
(** * Multisets of action triplets as lists *)
(** *)


Definition mBta := Map[Bta,nat].

Definition mBta_emp : mBta := (empty nat).
                                     
Definition mBta_singleton (a : Action) (d s : nat) : mBta := 
  add (mk_Bta a d s) 1 mBta_emp.

Parameter mBta_union : mBta -> mBta -> mBta.

Axiom mBta_union_correct :
  forall (x:Bta) (m1:mBta) (n1:nat),
    find x m1 = Some n1  ->
    forall m2 n2, find x m2 = Some n2 ->
             find x (mBta_union m1 m2) = Some (n1 + n2).

Axiom mBta_union_inv :
  forall x m1 m2 n,
    find x (mBta_union m1 m2) = Some n ->
    exists n1, find x m1 = Some n1 -> exists n2, find x m2 = Some n2 -> n = n1 + n2.
    

Definition Offset_MS_ActEx (s : m_eAction) (t : nat) : m_eAction :=
  let f := (s) in
  
  Bag (fun x : eAction => if f x >= 1 then
                         0

         f (eAction_off x t)match eAction_eq_dec (eAction_off a t) x with
                       | left _ => multiplicity a
                       | right _ => 0
                       end).
