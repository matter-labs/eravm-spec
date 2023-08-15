Require Coder Memory lib.Decidability.

Import Memory Coder Common ZMod.

Section Def.
  Import ZArith.
  Context {word: Type}.
  Context {ins_type: Type} (invalid_ins: ins_type).


  (** # Versioned hash

[%versioned_hash] is a hash augmented with additional information. It is used as
a key to identify the contract code for decommitter.

Additional information includes:

- [%VERSION_BYTE] (currently 1)
- [%marker] (is the contract being constructed or already constructed?)

The hash itself is described by [%partial_hash]; it is computed as SHA256 hash
modulo $2^{28 \times 8}$.

   *)
  Definition VERSION_BYTE: u8 := int_mod_of _ 1%Z.
  Inductive marker := CODE_AT_REST | YET_CONSTRUCTED | INVALID.
  Definition marker_valid (m: marker) :=
    match m with
    | INVALID => false
    | _ => true
    end.

  Record versioned_hash := mk_vhash {
                               code_length_in_words: u16;
                               extra_marker: marker;
                               partial_hash: int_mod (28*bits_in_byte)%nat
                             }.

  Axiom hash_coder: @coder word versioned_hash.

  (** EraVM accepts [%DEFAULT_AA_VHASH] as a parameter. See also [%Parameters]. *)
  Parameter DEFAULT_AA_VHASH: versioned_hash.


  (* begin hide *)
  Theorem eq_dec: Decidability.eq_dec versioned_hash.
  Proof.
    unfold Decidability.eq_dec.
    Decidability.decide_equality.
    apply ZMod.eq_dec.
    apply ZMod.eq_dec.
  Qed.

  (* end hide *)
End Def.
