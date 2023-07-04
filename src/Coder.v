Section Encoding.

(** # Encoding

Application Binary Interfaces (ABI) require describing serialization and deserialization.

- Serialization encodes an instance of type [T] into a word of type [word].
- Deserialization tries to decode an instance of type [T] from a word of type [word].
*)

Context {word T:Type}.

(** Definition [decoder] defines an embedding of a subset of words of type
[word] to a type [T]. Decoding may fail if the input word is malformed. *)
Definition decoder := word -> option T.

(** Definition [encoder] defines an embedding of type [T] to a set of possible [word] values.
 Encoding always succeeds. *)
Definition encoder := T -> word.

(** The record [coder] connects a specific decoder with the matching encoder, and proofs of their properties.

- [revertible1] formalizes the following: if we encode an element [t] of type [T] to a word, and then decode this word, the result will be [t] again.
- [revertible2] formalizes the following: if we successfully decoded an element [t] of type [T] from a word [w], and then encode [t] again, the encoding will match [w] again. *)
Record coder  := {
    decode: decoder;
    encode:  encoder;

    (** [decode] and [encode] should be mutual inverses. *)
    revertible1: forall params, decode (encode params) = Some params;
    revertible2: forall params encoded, decode encoded = Some params -> encode params = encoded;
  }.
End Encoding.
