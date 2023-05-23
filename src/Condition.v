Require Common.

Import Bool ZArith Common ZMod.

(** * Execution *)

Section Flags.

  Inductive OF_LT := Set_OF_LT | Clear_OF_LT.
  Inductive EQ := Set_EQ | Clear_EQ.
  Inductive GT := Set_GT | Clear_GT.

  Definition OF_LT_to_bool (f:OF_LT) := if f then true else false.
  Definition EQ_to_bool (f:EQ) := if f then true else false.
  Definition GT_to_bool (f:GT) := if f then true else false.

  #[reversible]
    Coercion OF_LT_to_bool : OF_LT >-> bool.
  #[reversible]
    Coercion EQ_to_bool : EQ >-> bool.
  #[reversible]
    Coercion GT_to_bool : GT >-> bool.

  Definition EQ_of_bool (f:bool) := if f then Set_EQ else Clear_EQ.
  Definition OF_LT_of_bool (f:bool) := if f then Set_OF_LT else Clear_OF_LT.
  Definition GT_of_bool (f:bool) := if f then Set_GT else Clear_GT.

  Record flags_state := mk_fs {
                            fs_OF_LT: OF_LT;
                            fs_EQ: EQ;
                            fs_GT: GT;
                          }.

  Definition set_overflow fs := match fs with
                              | mk_fs _ EQ GT => mk_fs Set_OF_LT EQ GT
                              end.

  Definition flags_clear : flags_state := mk_fs Clear_OF_LT Clear_EQ Clear_GT.
End Flags.

Section Conditions.
  Inductive cond :=
  | IfAlways | IfGT | IfEQ | IfLT | IfGE | IfLE | IfNotEQ | IfGTOrLT.

  Definition cond_holds (c:cond) (fs:flags_state) : bool :=
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

  Inductive cond_spec:  cond -> flags_state -> Prop
    :=
  | ac_Always: forall fs,
      cond_spec IfAlways fs

  | ac_GT: forall of_lt eq,
      cond_spec IfGT (mk_fs of_lt eq Set_GT)

  | ac_EQ: forall of_lt gt,
      cond_spec IfEQ (mk_fs of_lt Set_EQ gt)

  | ac_LT: forall eq gt,
      cond_spec IfLT (mk_fs Set_OF_LT eq gt)

  | ac_GE1: forall fs,
      cond_spec IfEQ fs ->
      cond_spec IfGE fs

  | ac_GE2: forall fs,
      cond_spec IfGT fs ->
      cond_spec IfGE fs

  | ac_LE1: forall fs,
      cond_spec IfLT fs ->
      cond_spec IfLE fs
  | ac_LE2: forall fs,
      cond_spec IfEQ fs ->
      cond_spec IfLE fs

  | ac_NotEQ: forall of_lt gt,
      cond_spec IfNotEQ (mk_fs of_lt Clear_EQ gt)

  | ac_IfGTOrLT1: forall fs,
      cond_spec IfGT fs->
      cond_spec IfGTOrLT fs

  | ac_IfGTOrLT2: forall fs,
      cond_spec IfLT fs->
      cond_spec IfGTOrLT fs
  .

  Hint Constructors cond_spec:flags.

  Theorem cond_holds_spec :
    forall c fs, cond_holds c fs = true <-> cond_spec c fs.
  Proof.
    split; destruct c, fs as [[] [] []];
      simpl in *; try solve [auto with flags| inversion 1; inversion H0].
  Qed.

  Theorem cond_activated_dec: forall ec flags, Decidability.dec (cond_spec ec flags).
  Proof.
    intros ec flags.
    unfold Decidability.dec.
    destruct ec, flags as [[][][]]; solve [left;constructor| right;inversion 1 | auto with flags | right; inversion 1; subst; inversion H0].
  Defined.

End Conditions.
