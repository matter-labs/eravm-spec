Require Coder Memory lib.Decidability.

Import Memory Coder Common ZMod.

Section Def.
  Context {word: Type}.
  Context {ins_type: Type} (invalid_ins: ins_type).

  
  Inductive marker := CODE_AT_REST | YET_CONSTRUCTED | INVALID.
  Definition marker_valid (m: marker) :=
    match m with
    | INVALID => false
    | _ => true
    end.
  
  Record versioned_hash := mk_vhash {
                               code_length_in_words: u16;
                               extra_marker: marker;
                               partial_hash: int_mod (28*8)%nat
                             }.
  
  Axiom hash_coder: @coder word versioned_hash.
  Parameter DEFAULT_AA_VHASH: versioned_hash.
  Parameter DEFAULT_AA_CODE: code_page invalid_ins.
  
  Theorem eq_dec: Decidability.eq_dec versioned_hash.
  Proof.
    unfold Decidability.eq_dec.
    Decidability.decide_equality.
    apply ZMod.eq_dec.
    apply ZMod.eq_dec.
  Qed.
End Def.
