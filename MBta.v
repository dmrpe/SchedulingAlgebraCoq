Definition mBta := Map[Bta,nat].
    
Definition eAction_off (a:eAction)(t:nat) : eAction :=
  mk_eAction (act a) (dur a) (stt a + t).

(** *)
(** * Multisets of action triplets as lists *)
(** To replace in the future by a better model. *)
(** *)

Definition m_eAction := multiset eAction.

Definition emp_m_eAction : m_eAction := EmptyBag eAction.
                                     
Definition singleton_eAction (a : Action) (d s : nat) : m_eAction := 
  SingletonBag (@eq eAction) eAction_eq_dec (mk_eAction a d s).

Definition Union_MS_ActEx (a b : m_eAction) : m_eAction := munion a b.

Definition Offset_MS_ActEx (s : m_eAction) (t : nat) : m_eAction :=
  let f := (s) in
  
  Bag (fun x : eAction => if f x >= 1 then
                         0

         f (eAction_off x t)match eAction_eq_dec (eAction_off a t) x with
                       | left _ => multiplicity a
                       | right _ => 0
                       end).
