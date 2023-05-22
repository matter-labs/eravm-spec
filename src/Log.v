Require Decidability List.
Import Decidability.

Section Log.
  Variable T:Type.
  Hypothesis elem_dec: Decidability.eq_dec T.
  Definition log := list T.

  Definition contains (l:log) (elem:T): bool := if List.in_dec elem_dec elem l then true else false.

  Inductive contains_spec (l: log) (elem: T) : bool -> Prop :=
  | cs_fresh : List.In elem l -> contains_spec l elem true
  | cs_not_fresh : (~ List.In elem l) -> contains_spec l elem false.

  
  Theorem contains_spec_correct :
    forall cm p b, contains cm p = b <-> contains_spec cm p b.
  Proof.
    unfold contains.
    split.
    - intros H.
      destruct (List.in_dec _ _ _); subst; constructor; assumption.
    - inversion 1; subst;
        destruct (List.in_dec _ _ _); solve [reflexivity|contradiction].
  Qed.

End Log.
