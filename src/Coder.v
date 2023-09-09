Require Common.
Import ssreflect ssrfun.

Section Encoding.

(** # Encoding

Application Binary Interfaces ([%ABI]) require describing serialization and
deserialization.

- Serialization encodes an instance of type [%T] into a word of type [%word].
- Deserialization tries to decode an instance of type [%T] from a word of type
  [%word].
   *)

  Context {U T:Type}.

  (** The type [%decoder] defines an embedding of a subset of words of type
[%word] to a type [%T]. Decoding may fail if the input word is malformed. *)
  Definition decoder := U -> option T.

  (** Definition [%encoder] defines an embedding of type [%T] to a set of possible
[%word] values.
   *)
  Definition encoder := T -> option U.

  Definition revertible (decode:decoder) (encode:encoder):= forall obj encoded, encode obj = Some encoded -> decode encoded = Some obj.

  (** The record [%coder] connects a specific decoder with the matching encoder,
and proofs of their properties.

- [%revertible decode encode] formalizes the following: if we encode an element [%t] of type
   *)
  Record coder  := mk_coder {
      decode: decoder;
      encode:  encoder;

      (** [%decode] and [%encode] should be mutual inverses in the following
    sense: *)
      _: revertible decode encode;
    }.
End Encoding.

Section Properties.

  Context {A B C: Type}.

  Section PropertyComposition.
    Context (encode1: @encoder B A) (decode1:@decoder B A) (encode2: @encoder C B) (decode2: @decoder C B).

    Theorem revertible1_compose:
      revertible decode1 encode1 ->
      revertible decode2 encode2 ->
      let encode3 : A -> option C := pcomp encode2 encode1 in
      let decode3 : C -> option A := pcomp decode1 decode2 in
      revertible decode3 encode3.
    Proof.
      unfold revertible, pcomp, obind, oapp.
      move => H1 H2 params encoded.
      case_eq (encode1 params);
        by [move => ? ? ?; erewrite H2; eauto| done].
    Qed.

  End PropertyComposition.

  Definition coder_compose (c2: @coder C B) (c1: @coder B A) : @coder C A.
    refine (mk_coder  (pcomp (decode c1) (decode c2)) (pcomp (encode c2) (encode c1)) _).
    by destruct c1, c2; eapply revertible1_compose; eauto.
  Defined.
End Properties.
