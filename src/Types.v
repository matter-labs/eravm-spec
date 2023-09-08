Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect.ssreflect.
From Bits Require Import bits.
Export ssreflect spec.

Set Warnings "notation-overridden,ambiguous-paths".
(** # Common project-independent definitions *)
Section Types.
  Import ZArith bits.
  (** ## Unsigned numbers

Unsigned integers modulo $2^n$.

Type $u_N$ holds integers in range from 0 inclusive to $2^N$ exclusive.

Definitions [%uN_of] are constructors of [%uN] types; they accept an integer and
return its value modulo $2^N$ packed in a type [%int_mod N].
   *)
  Definition u8 := BITS 8.
  Definition u8_of := @fromZ 8.

  Definition u16 := BITS 16.
  Definition u16_of := @fromZ 16.

  Definition u24 := BITS 24.
  Definition u24_of := @fromZ 24.

  Definition u32 := BITS 32.
  Definition u32_of := @fromZ 32.

  Definition u64 := BITS 64.
  Definition u64_of := @fromZ 64.

  Definition u128 := BITS 128.
  Definition u128_of := @fromZ 128.

  Definition u160 := BITS 160.
  Definition u160_of := @fromZ 160.

  Definition u192 := BITS 192.
  Definition u192_of := @fromZ 192.

  Definition u224 := BITS 224.
  Definition u224_of := @fromZ 224.

  Definition u256 := BITS 256.
  Definition u256_of := @fromZ 256.


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

  (** The definition [%bits_in_byte] is provided for readability.*)
  Definition bits_in_byte : nat  := 8%nat.

End Types.
