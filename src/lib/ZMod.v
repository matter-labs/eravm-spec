Require ZArith ZArith_ext ZBits.

Import BinInt ZArith ZArith_ext BinIntDef.Z.



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
                              int_range: in_range 0 int_val characteristic = true
                            }.

  (** Equality *)

  Lemma eq_values: forall (x y: int_mod),
      x = y <-> int_val x = int_val y.
  Proof.
    intros x y; split.
    - intros; subst; reflexivity.
    - destruct x,y.
      simpl in *.
      intros ?; subst.
      f_equal.
      destruct (in_range 0 int_val1 characteristic); [|discriminate].
      rewrite (Eqdep_dec.UIP_refl_bool _ int_range1).
      rewrite (Eqdep_dec.UIP_refl_bool _ int_range0).
      reflexivity.
  Qed.

  Theorem eq_dec : Decidability.eq_dec int_mod.
  Proof.
    intros [x xp] [y yp].
    destruct (Z.eq_dec x y); subst.
    - left.
      apply eq_values. reflexivity.
    - right.
      intro H. subst. apply eq_values in H. contradiction.
  Qed.
    
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
  Definition int_mod_of (z: Z) : int_mod.
    pose (truncated := ZArith_ext.mod_pow2 z bits).
    refine (mk_int_mod truncated _).
    apply in_range_spec_l.
    apply (int_mod_range z).
  Defined.

  (** ** Operations *)
  (** Addition, subtraction, multiplication, division, shifts, modulo operations. *)

  (** *** Comparison *)
  Definition beq (x y: int_mod) : bool := if eq_dec x y then true else false.
  Definition lt_signed (x y: int_mod) : bool := if lt_dec (as_signed x) (as_signed y) then true else false.
  Definition lt_unsigned (x y: int_mod) : bool := if lt_dec (as_unsigned x) (as_unsigned y) then true else false.
  Definition gt_unsigned := Basics.flip lt_unsigned.

  Definition le_unsigned (x y: int_mod) : bool := (lt_unsigned x y) || beq x y.
  Definition ge_unsigned := Basics.flip le_unsigned.

  Definition liftZ  (f:Z->Z->Z) x y := int_mod_of (f x.(int_val) y.(int_val)).

  Definition min := liftZ BinIntDef.Z.min.
  Definition max := liftZ BinIntDef.Z.max.
  
  Definition carry (z:Z) : bool := if gt_dec z unsigned_max then true else false.

  Definition uadd_overflow (x y: int_mod) : int_mod * bool :=
    let result := (as_unsigned x + as_unsigned y)%Z in
    (int_mod_of result, carry result).

  Definition uinc_overflow (x: int_mod) : int_mod * bool :=
    uadd_overflow x (int_mod_of 1).

  Definition usub_overflow (x y: int_mod) : int_mod * bool :=
    let a := as_unsigned x in
    let b := as_unsigned y in
    (int_mod_of (a-b)%Z, if gt_dec b a then true else false).

  Definition is_overflowing (res: int_mod * bool) := snd res.

  Definition umul_overflow (x y: int_mod) : int_mod * bool :=
    let result := (as_unsigned x * as_unsigned y)%Z in
    (int_mod_of result, carry result).
  
End Def.


Definition beq_op {n:nat} (x y: int_mod n) : bool := beq n x y.

Declare Scope ZMod_scope.
Infix "==" := beq_op (at level 70, no associativity): ZMod_scope.
Infix "+" := (uadd_overflow _) : ZMod_scope.
Infix "-" := (usub_overflow _) : ZMod_scope.
Infix "*" := (umul_overflow _) : ZMod_scope.

Open Scope ZMod_scope.

Definition bitwise_op (f:Z->Z->Z) (bits:nat) (x y: int_mod bits) : int_mod bits :=
  int_mod_of _ (f (int_val _ x) (int_val _ y)).

Definition bitwise_xor := bitwise_op lxor.
Definition bitwise_or  := bitwise_op lor.
Definition bitwise_and := bitwise_op land.


Definition resize (sz1 sz2:nat) (x: int_mod sz1) : int_mod sz2 :=
  int_mod_of sz2 (int_val sz1 x).


Definition mix_lower n (source: int_mod (n+n) ) (mix: int_mod n) : int_mod (n+n) :=
  (
    let p := Z.of_nat n in
    let hi := source.(int_val _) / (2^p) in
    int_mod_of (n+n) ( hi * (2^p) + mix.(int_val _))) %Z.
