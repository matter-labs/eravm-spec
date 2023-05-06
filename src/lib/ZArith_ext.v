Require Coq.Logic.Decidable.
Require Decidability.
Require PArith.
Require PArith_ext.
Require ZArith.
Require Lia.

(** * Properties of Z *)

Section Decidability.
  (** ** Decidability *)
  Import Decidability ZArith.

  Lemma eq_dec : eq_dec BinNums.Z.
    decide_equality.
  Defined.

  Open Scope Z_scope.
  Definition lt_dec: forall (x y: Z), {x < y} + {x >= y}.
  Proof.
    unfold Z.lt, Z.ge.
    intros x y; destruct (Z.compare x y); auto; right; intro H; inversion H.
  Defined.

  Definition gt_dec: forall (x y: Z), {x > y} + {x <= y}.
  Proof.
    unfold Z.gt, Z.le.
    intros x y; destruct (Z.compare x y); auto; right; intro H; inversion H.
  Defined.

End Decidability.


Section ModuloPowerOfTwo.
  Import ZArith.
  Import PArith_ext.
  Open Scope Z.

  Definition mod_pow2 (z: Z) (n: nat) : Z :=
    match z with
    | Z0 => 0
    | Zpos p => mod_pow2 p n
    | Zneg p => let r := mod_pow2 p n in
               if ZArith_ext.eq_dec r 0%Z
               then 0
               else ZArith.Zpower.two_power_nat n - r
    end.


  Theorem mod_pow2_ge_0:
    forall z n, mod_pow2 z n >= 0.
  Proof.
    intros. unfold mod_pow2. pose ( Arith_ext.two_power_nat_gt_0 n) as Hpos.
    destruct z.
    - auto with zarith.
    - exact (PArith_ext.mod_pow2_ge_0 p n).
    - destruct (eq_dec _ 0) .
      + auto with zarith.
      + pose (PArith_ext.mod_pow2_ge_0 p n).
        pose (PArith_ext.mod_pow2_limit p n).
        Lia.lia.
  Qed.

  Theorem mod_pow2_limit:
    forall z n, mod_pow2 z n < two_power_nat n.
  Proof.
    intros. unfold mod_pow2. pose ( Arith_ext.two_power_nat_gt_0 n) as Hpos.
    destruct z.
    - auto with zarith.
    - pose (PArith_ext.mod_pow2_limit p n). auto with zarith.
    - destruct (eq_dec _ 0) .
      + auto with zarith.
      + pose (PArith_ext.mod_pow2_ge_0 p n).
        pose (PArith_ext.mod_pow2_limit p n).
        Lia.lia.
  Qed.

  Theorem mod_pow2_range:
    forall z n, 0 <= mod_pow2 z n < two_power_nat n.
  Proof.
    split.
    - apply Z.ge_le. apply mod_pow2_ge_0.
    - apply mod_pow2_limit.
  Qed.

  (* Lemma mod_modulus_range: *)
  (*   forall x, 0 <= Z_mod_modulus x < characteristic. *)
  (* Proof (Z_mod_two_p_range bits). *)

  (* Lemma Z_mod_modulus_range': *)
  (*   forall x, -1 < Z_mod_modulus x < modulus. *)
  (* Proof. *)

  (*   Lemma Z_mod_modulus_eq: *)
  (*     forall x, Z_mod_modulus x = x mod modulus. *)
  (*   Proof (Z_mod_two_p_eq wordsize). *)


  Close Scope Z_scope.
End ModuloPowerOfTwo.

Section Range.
Import ZArith.
Definition in_range (x y z:Z) : bool :=
  if Z_le_dec x y then
    if Z_lt_dec y z then true
    else false
  else false.

Theorem in_range_spec_l:
  forall x y z, (x <= y < z)%Z -> in_range x y z = true.
Proof.
unfold in_range; intros x y z [H H'].
destruct (Z_le_dec _ _); auto.
destruct (Z_lt_dec _ _); auto.
Qed.

Theorem in_range_spec_r:
  forall x y z, in_range x y z = true -> (x <= y < z)%Z.
Proof.
  unfold in_range.
  intros x y z H.
  destruct (Z_le_dec _ _); try destruct (Z_lt_dec _ _); auto; try discriminate.
Qed.

End Range.
#[export]
  Hint Resolve  eq_dec gt_dec lt_dec: decidable_prop.
