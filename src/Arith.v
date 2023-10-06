From mathcomp Require ssreflect ssrfun ssrbool eqtype tuple zmodp.
Require Types.
Set Warnings "-notation-overridden,-ambiguous-paths".
Import Types ssreflect.tuple ssreflect.eqtype ssrbool.
Set Warnings "notation-overridden,ambiguous-paths".

(** # Common project-independent definitions *)

Section Operations.
  Import operations ZArith.

  Record udiv_result {n} := mk_divrem { div: BITS n; rem: BITS n }.

  Definition uadd_of {n: nat} (a: BITS n) (b:BITS n) : bool * BITS n := adcB false a b.
  Definition uadd_wrap {n: nat} (a: BITS n) (b:BITS n) : BITS n := snd (uadd_of a b).
  Definition uinc_of {n: nat} (a: BITS n) : bool * BITS n := uadd_of a (fromZ 1).
  Definition uinc_by_32_of {n: nat} (a: BITS n) : bool * BITS n := uadd_of a (fromZ 32).

  Definition usub_uf {n: nat} (a: BITS n) (b:BITS n) : bool * BITS n := sbbB false a b.
  Definition umul {n: nat} (a: BITS n) (b:BITS n) : BITS (n+n) := fullmulB a b.

  Definition udiv {n: nat} (a: BITS (S n)) (b:BITS (S n)) : udiv_result :=
    let za := toZ a in
    let zb := toZ b in
    @mk_divrem (S n) (fromZ (BinInt.Z.div za zb)) (fromZ (BinInt.Z.rem za zb)).

  Definition lt_unsigned {n:nat} (a b: BITS n) := ltB a b.
  Definition gt_unsigned {n:nat} (a b: BITS n) := lt_unsigned b a.
  Definition le_unsigned {n:nat} (a b: BITS n) := lt_unsigned a b || (a == b).
  Definition ge_unsigned {n:nat} (a b: BITS n) := gt_unsigned a b || (a == b).

  Definition bitwise_xor {n} := @xorB n.
  Definition bitwise_or  {n} := @orB n.
  Definition bitwise_and {n} := @andB n.

  Definition characteristic (n:nat): Z := 2 ^ (Z.of_nat n).
  Definition unsigned_max (n:nat) :Z := characteristic n - 1.
  Definition unsigned_min :Z := 0.

  Definition min {n} (a b: BITS n) : BITS n := if lt_unsigned a b then a else b.
  Definition max {n} (a b: BITS n) : BITS n := if gt_unsigned a b then a else b.

  Definition widen {s} (result_size: nat) (val: BITS s): BITS (s + (result_size - s)) :=  @zeroExtend (result_size - s)%nat s  val.

  Definition rolBn {n} (p: BITS (S n)) (k: nat): BITS (S n) := Nat.iter k rolB p.
  Definition rorBn {n} (p: BITS (S n)) (k: nat): BITS (S n) := Nat.iter k rorB p.

  Definition subrange_len {skip} (from:nat) (len:nat) (w:BITS ((from + len) + skip))  :=
    (@high len from (@low skip (ssrnat.addn from len) w)).

  Definition subrange {skip} (from:nat) (to:nat) (w:BITS (from + (to-from) + skip))  :=
    @subrange_len skip from (to-from) w.

End Operations.

Declare Scope ZMod_scope.

Infix "+" := (uadd_of) : ZMod_scope.
Infix "-" := (usub_uf) : ZMod_scope.
Infix "*" := (umul) : ZMod_scope.
Infix "<" := (lt_unsigned ) : ZMod_scope.
Infix ">" := (gt_unsigned) : ZMod_scope.
Infix "<=" := (le_unsigned) : ZMod_scope.
Infix ">=" := (ge_unsigned) : ZMod_scope.
(* Equality is already provided by [%eqType] of ssreflect.  *)

Notation "w  { from , to }" := (@subrange _ from to w) (at level 10) : ZMod_scope .

Bind Scope ZMod_scope with BITS.
