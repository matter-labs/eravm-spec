Require Coder Memory.

Section Def.
  Import ZArith ssrbool eqtype ssreflect ssrfun ssrbool ssreflect.eqtype ssreflect.tuple zmodp.
  Import Memory Coder Common.

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
  Definition VERSION_BYTE: u8 := fromZ 1%Z.

  Inductive marker := CODE_AT_REST | YET_CONSTRUCTED | INVALID.

  (* begin details: decidable equality *)
  Scheme Equality for marker.
  Lemma marker_eqP : Equality.axiom marker_beq.
  Proof. by move => [] []; constructor. Qed.

  Canonical marker_eqMixin := EqMixin marker_eqP.
  Canonical marker_eqType := Eval hnf in EqType marker marker_eqMixin.
  (* end details *)

  Definition marker_valid (m: marker) :=
    match m with
    | INVALID => false
    | _ => true
    end.

  Record versioned_hash := mk_vhash {
                               code_length_in_words: u16;
                               extra_marker: marker;
                               partial_hash: BITS (28*bits_in_byte)%nat
                             }.
  Axiom hash_coder: @Coder.coder word versioned_hash.

  (** EraVM accepts [%DEFAULT_AA_VHASH] as a parameter. See also [%Parameters]. *)
  Parameter DEFAULT_AA_VHASH: versioned_hash.

  Open Scope ZMod_scope.

  (* begin details: equality on versioned hashes *)
  Definition eqn (x y:versioned_hash) : bool :=
    match x,y with
    | mk_vhash l1 em1 ph1 , mk_vhash l2 em2 ph2 =>
        (l1 == l2) && (em1 == em2) && (ph1 == ph2)
    end.

  Lemma eqnP : Equality.axiom eqn.
  Proof.
    move => [l1 em1 ph1] [l2 em2 ph2].
    simpl.
    destruct (l1 == l2) eqn: H1;
      destruct (em1 == em2) eqn: H2;
      destruct (ph1 == ph2) eqn: H3;
      try move: (eqP H1) => ->; try move: (eqP H2) => ->; try move: (eqP H3) => ->; constructor =>//.
    - injection. move => ?; subst. by rewrite eq_refl in H3.
    - injection. move => ?; subst. by rewrite eq_refl in H2.
    - injection. move => ?; subst. by rewrite eq_refl in H3.
    - injection. move => ?; subst. by rewrite eq_refl in H1.
    - injection. move => ?; subst. by rewrite eq_refl in H3.
    - injection. move => ?; subst. by rewrite eq_refl in H2.
    - injection. move => ?; subst. by rewrite eq_refl in H3.
  Qed.

  Canonical vh_eqMixin := EqMixin eqnP.
  Canonical vh_eqType := Eval hnf in EqType _ vh_eqMixin.

  (* end details *)
End Def.
