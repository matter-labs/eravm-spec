Section Encoding.

Context {word ABIParams:Type}.

(** # Encoding

Describing ABIs requires describing serialization and deserialization.
Record [coder] defines an embedding of type [ABIParams] to a set of possible [word] values.
 *)

(** Decoding may  . *)
Definition decoder := word -> option ABIParams.
(** Encoding always succeeds. *)
Definition encoder := ABIParams -> word.

Record coder  := {
    decode: decoder;
    encode:  encoder;

    (** [decode] and [encode] should be mutual inverses. *)
    revertible1: forall params, decode (encode params) = Some params;
    revertible2: forall params encoded, decode encoded = Some params -> encode params = encoded;
  }.
End Encoding.  
