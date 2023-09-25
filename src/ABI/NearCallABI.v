Require Coder Ergs Memory.

Import ssreflect.
Import Types Core Coder Ergs Memory.

Section NearCallABI.
Record params: Type :=
  mk_params {
      ergs_passed: u32;
    }.

Definition encode : params -> option u32 := fun p => Some p.(ergs_passed).
Definition decode : u32 -> option params := fun u => Some (mk_params u).

Definition encode_word (p:params) (high224: u224) : option word :=
  option_map (fun encoded => high224 ## encoded) (encode p).

Definition decode_word (w:word) : option (u224 * params) :=
  option_map (fun decoded => (@high 224 32 w, decoded)) (decode (low 32 w)).

Definition coder : @coder u32 params.
refine (mk_coder decode encode _).
unfold revertible, encode, decode.
by move => []; inversion 1.
Defined.
End NearCallABI.
