Require Decidability List.
Import Decidability.

Section History.

  (** # History
**History** is a data structure supporting appending elements of type [%T] to it.
   *)
  Context (T:Type) (elem_dec: Decidability.eq_dec T).

  Definition history := list T.

  Context (l:history).

  (** [%history] supports checking if an element is contained in it. *)
  Definition contains (elem:T): bool := if List.in_dec elem_dec elem l then true else false.

  Inductive contains_spec (elem: T) : bool -> Prop :=
  | cs_fresh : List.In elem l -> contains_spec elem true
  | cs_not_fresh : (~ List.In elem l) -> contains_spec elem false.


  Theorem contains_spec_correct :
    forall p b, contains p = b <-> contains_spec p b.
  Proof.
    unfold contains.
    split.
    - intros H.
      destruct (List.in_dec _ _ _); subst; constructor; assumption.
    - inversion 1; subst;
        destruct (List.in_dec _ _ _); solve [reflexivity|contradiction].
  Qed.

End History.
