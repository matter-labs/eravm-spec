Require Flags.

Import Bool Common Flags.

Section Predication.
  (** # Predication

Every instruction on the [%code_page] is predicated, meaning it is augmented with a [%predicate].
A predicate describes a condition on flags; if this condition is satisfied, then the instruction is executed; otherwise, it is skipped.

When an instruction is skipped, its base cost is still paid. *)
  Inductive predicate : Set :=
  | IfAlways | IfGT | IfEQ | IfLT | IfGE | IfLE | IfNotEQ | IfGTOrLT.

  Definition predicate_holds (c:predicate) (fs:flags_state) : bool :=
    match c, fs with
    | IfAlways, _
    | IfGT, mk_fs _ _  Set_GT
    | IfEQ, mk_fs _ Set_EQ _
    | IfLT, mk_fs Set_OF_LT _ _
    | IfGE, mk_fs _ Set_EQ _
    | IfGE, mk_fs _ _ Set_GT
    | IfLE, mk_fs _ Set_EQ _
    | IfLE, mk_fs Set_OF_LT _ _
    | IfNotEQ, mk_fs _ Clear_EQ _
    | IfGTOrLT,mk_fs Set_OF_LT _ _
    | IfGTOrLT,mk_fs _ _ Set_GT => true
    | _,_ => false
    end.

  Inductive predicate_spec:  predicate -> flags_state -> Prop
    :=
  | ac_Always: forall fs,
      predicate_spec IfAlways fs

  | ac_GT: forall of_lt eq,
      predicate_spec IfGT (mk_fs of_lt eq Set_GT)

  | ac_EQ: forall of_lt gt,
      predicate_spec IfEQ (mk_fs of_lt Set_EQ gt)

  | ac_LT: forall eq gt,
      predicate_spec IfLT (mk_fs Set_OF_LT eq gt)

  | ac_GE1: forall fs,
      predicate_spec IfEQ fs ->
      predicate_spec IfGE fs

  | ac_GE2: forall fs,
      predicate_spec IfGT fs ->
      predicate_spec IfGE fs

  | ac_LE1: forall fs,
      predicate_spec IfLT fs ->
      predicate_spec IfLE fs
  | ac_LE2: forall fs,
      predicate_spec IfEQ fs ->
      predicate_spec IfLE fs

  | ac_NotEQ: forall of_lt gt,
      predicate_spec IfNotEQ (mk_fs of_lt Clear_EQ gt)

  | ac_IfGTOrLT1: forall fs,
      predicate_spec IfGT fs->
      predicate_spec IfGTOrLT fs

  | ac_IfGTOrLT2: forall fs,
      predicate_spec IfLT fs->
      predicate_spec IfGTOrLT fs
  .
(* begin details: proofs *)
  Hint Constructors predicate_spec:flags.

  Theorem predicate_holds_spec :
    forall c fs, predicate_holds c fs = true <-> predicate_spec c fs.
  Proof.
    split; destruct c, fs as [[] [] []];
      simpl in *; try solve [auto with flags| inversion 1; inversion H0].
  Qed.

  Theorem predicate_activated_dec: forall ec flags, Decidability.dec (predicate_spec ec flags).
  Proof.
    intros ec flags.
    unfold Decidability.dec.
    destruct ec, flags as [[][][]]; solve [left;constructor| right;inversion 1 | auto with flags | right; inversion 1; subst; inversion H0].
  Defined.

(* end details *)


  Record predicated (instruction:Type): Type :=
    Ins {
        ins_spec: instruction;
        ins_cond: predicate;
      }.

  (** Invalid instruction. It is a default value on code memory pages. See
  [%code_page]. It is parameterized by an instruction type for convenience of
  defining it. *)

  Definition invalid {I} (ins:I) : predicated I :=
    {|
      ins_spec := ins;
      ins_cond:= IfAlways
    |}.

End Predication.
