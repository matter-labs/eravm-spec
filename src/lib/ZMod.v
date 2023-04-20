Require ZArith ZArith_ext.

Import BinInt ZArith ZArith_ext.


  (** * Machine integers modulo 2^N.
      Integers are encoded in binary form (see [BinNums.positive]), therefore we are able to
      efficiently reason about wide numbers e.g. 256-bit. *)
Section Def.

  (** [bits] is an implicit parameter passed to all definitions in this section
  that use it. After the Section end, all definitions will be rewritten so that
  [bits] is passed to them explicitly. *)
  Variable bits: nat.
  
  (** [bits_nz] is an implicit proof passed to all definitions in this section
  that use it. It forbids constructing integers modulo 1. After the Section end,
   all definitions will be rewritten so that [bits] is passed to them explicitly. *)
  Hypothesis bits_nz: (bits <> 0)%nat.


  (* [Let] is a keyword for section-local definitions, to be inlined. *)
  Let zbits: Z :=  Z.of_nat bits.
  Let characteristic: Z := 2 ^ zbits.


  (** An integer modulo 2^N. It carries a proof [int_range] of representability
  with no more than [bits] binary digits. *)
  Record int_mod: Type := mk_int_mod {
                              int_val: Z;
                              int_range: (0 <= int_val < characteristic)%Z
                            }.

  (** ** Conversions *)

  (** Interpreting [int_mod] as an unsigned integer modulo 2^N. *)
  Definition as_unsigned (n: int_mod) : Z := int_val n.

  (** Interpreting [int_mod] as a signed [Z], where the leftmost bit encodes the
  sign. *)
  Definition as_signed (n: int_mod) : Z :=
    (let x := as_unsigned n in
     if lt_dec x (characteristic/2) then x else x - characteristic)%Z.

  (** Minimal unsigned value.  *)
  Definition unsigned_min: Z := 0.
  (** Maximal unsigned value. *)
  Definition unsigned_max : Z := characteristic - 1.
  (** Minimal signed value. *)
  Definition signed_min : Z := - (characteristic / 2).
  (** Maximal signed value. *)
  Definition signed_max : Z := (characteristic / 2) - 1.



  (** An integer modulo 2^N falls in range between 0 inclusive and 2^N exclusive. *)
  Theorem int_mod_range:
    forall z : Z, (0 <= mod_pow2 z bits < characteristic)%Z.
  Proof.
    intros z.
    unfold characteristic, zbits.
    rewrite <-two_power_nat_equiv.
    apply mod_pow2_range.
  Qed.

  (** Ensure an integer is representable with N bits, truncating it if necessary. *)
  Definition mk_int_mod_truncated (z: Z) : int_mod :=
    let truncated := ZArith_ext.mod_pow2 z bits in
    mk_int_mod truncated (int_mod_range z).



  (** ** Operations *)
  (** Addition, subtraction, multiplication, division, shifts, modulo operations. *)

  (** *** Comparison *)
  Definition beq (x y: int_mod) : bool := if eq_dec (int_val x) (int_val y) then true else false.
  Definition lt_signed (x y: int_mod) : bool := if lt_dec (as_signed x) (as_signed y) then true else false.
  Definition lt_unsigned (x y: int_mod) : bool := if lt_dec (as_unsigned x) (as_unsigned y) then true else false.

  Definition carry (z:Z) : bool := if gt_dec z unsigned_max then true else false.

  Definition uadd_overflow (x y: int_mod) : int_mod * bool :=
    let result := (as_unsigned x + as_unsigned y)%Z in
    (mk_int_mod_truncated result, carry result).

  Definition uinc_overflow (x: int_mod) : int_mod * bool :=
    uadd_overflow x (mk_int_mod_truncated 1).

  Definition usub_overflow (x y: int_mod) : int_mod * bool :=
    let a := as_unsigned x in
    let b := as_unsigned y in
    (mk_int_mod_truncated (a-b)%Z, if gt_dec b a then true else false).

End Def.


Definition resize (sz1 sz2:nat) (x: int_mod sz1) : int_mod sz2 :=
  mk_int_mod_truncated sz2 (int_val sz1 x).

