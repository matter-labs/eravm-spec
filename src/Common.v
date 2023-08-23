Require lib.ZMod.

(** # Common project-independent definitions *)
Section Types.
  Import ZArith lib.ZMod.
  Let mk n := int_mod_of n.

  (** ## Unsigned numbers

Unsigned integers modulo $2^n$.

Type $u_N$ holds integers in range from 0 inclusive to $2^N$ exclusive.

Definitions [%uN_of] are constructors of [%uN] types; they accept an integer and return its value modulo $2^N$ packed in a type [%int_mod N].
   *)
  Definition u8 := int_mod 8.
  Definition u8_of := mk 8.

  Definition u16 := int_mod 16.
  Definition u16_of := mk 16.

  Definition u24 := int_mod 24.
  Definition u24_of := mk 24.

  Definition u32 := int_mod 32.
  Definition u32_of := mk 32.

  Definition u64 := int_mod 64.
  Definition u64_of := mk 64.

  Definition u128 := int_mod 128.
  Definition u128_of := mk 128.

  Definition u160 := int_mod 160.
  Definition u160_of := mk 160.

  Definition u256 := int_mod 256.
  Definition u256_of := mk 256.


  (** Definitions of zeros and ones for each fixed-width unsigned integer type. *)
  Definition zero8   := u8_of 0.
  Definition zero16  := u16_of 0.
  Definition zero24  := u24_of 0.
  Definition zero32  := u32_of 0.
  Definition zero64  := u64_of 0.
  Definition zero128 := u128_of 0.
  Definition zero160 := u160_of 0.
  Definition zero256 := u256_of 0.

  Definition one8   := u8_of 1.
  Definition one16  := u16_of 1.
  Definition one24  := u24_of 1.
  Definition one32  := u32_of 1.
  Definition one64  := u64_of 1.
  Definition one128 := u128_of 1.
  Definition one160 := u160_of 1.
  Definition one256 := u256_of 1.

End Types.

(** The definition [%bits_in_byte] is provided for readability.*)
Definition bits_in_byte : nat  := 8%nat.
