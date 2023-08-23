From Bits Require Import bits.
From mathcomp Require Import ssreflect ssrfun ssrbool.
Import eqtype.
(** # Common project-independent definitions *)
Section Types.
  Import ZArith bits.
  (** ## Unsigned numbers

Unsigned integers modulo $2^n$.

Type $u_N$ holds integers in range from 0 inclusive to $2^N$ exclusive.

Definitions [%uN_of] are constructors of [%uN] types; they accept an integer and return its value modulo $2^N$ packed in a type [%int_mod N].
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

  Definition uadd_of {n: nat} (a: BITS n) (b:BITS n) : bool * BITS n := adcB false a b.
  Definition usub_uf {n: nat} (a: BITS n) (b:BITS n) : bool * BITS n := sbbB false a b.


End Types.

Declare Scope ZMod_scope.
Locate  "==".
Import ZArith.
Axiom a : @BITS 8.
Import
Check (a == a).
Infix "==" := beq_op (at level 70, no associativity): ZMod_scope.
Infix "!=" := bneq_op (at level 70, no associativity): ZMod_scope.
Infix "+" := (uadd_overflow _) : ZMod_scope.
Infix "-" := (usub_overflow _) : ZMod_scope.
Infix "*" := (umul_overflow _) : ZMod_scope.

Infix "<" := (lt_unsigned _) : ZMod_scope.
Infix ">" := (gt_unsigned _) : ZMod_scope.
Infix "<=" := (le_unsigned _) : ZMod_scope.
Infix ">=" := (ge_unsigned _) : ZMod_scope.

Bind Scope ZMod_scope with int_mod.
Definition bitwise_op (f:Z->Z->Z) (bits:nat) (x y: int_mod bits) : int_mod bits :=
  int_mod_of _ (f (int_val _ x) (int_val _ y)).

Definition bitwise_xor := bitwise_op lxor.
Definition bitwise_or  := bitwise_op lor.
Definition bitwise_and := bitwise_op land.


Definition resize (sz1 sz2:nat) (x: int_mod sz1) : int_mod sz2 :=
  int_mod_of sz2 (int_val sz1 x).
(** The definition [%bits_in_byte] is provided for readability.*)
Definition bits_in_byte : nat  := 8%nat.
