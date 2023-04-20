Require BinNums BinInt ZArith Arith_ext.

(** * Additional properties of positive numbers *)


(** ** Power *)
Section ModuloPowerOfTwo.
Import Arith_ext BinNums BinInt ZArith Lia.

Open Scope Z_scope.


Fixpoint mod_pow2 (p: positive) (n: nat) {struct n} : Z :=
  match n, p with
  | O, _ => 0
  | S m, xH => 1
  | S m, xO tail => Z.double (mod_pow2 tail m)
  | S m, xI tail => Z.succ_double (mod_pow2 tail m)
  end.

Theorem mod_pow2_ge_0:
  forall p n, mod_pow2 p n >= 0.
Proof.
  induction p; destruct n; simpl; auto with zarith.
  - rewrite Z.succ_double_spec.
    apply Z.le_ge.
    apply Z.add_nonneg_nonneg; auto with zarith.
    replace 0 with ( 0 * mod_pow2 p n); [|auto with zarith].
    eapply Zmult_le_compat_r; [auto with zarith|].
    apply Z.ge_le.
    apply IHp.
  - rewrite Z.double_spec.
    replace 0 with ( 0 * mod_pow2 p n); [|auto with zarith].
    eapply Zmult_ge_compat_r; [auto with zarith|].
    apply IHp.
Qed.

Lemma mod_pow2_limit:
  forall p n, mod_pow2 p n < two_power_nat n.
Proof.
  intros p n; revert p.
  induction n; simpl; intros.
  - rewrite Arith_ext.two_power_nat_0. lia.
  - rewrite two_power_nat_S. destruct p.
    + pose (IHn p). rewrite Z.succ_double_spec. lia.
    + pose (IHn p). rewrite Z.double_spec. lia.
    + pose (two_power_nat_gt_0 n). lia.
Qed.


Close Scope Z_scope.
End ModuloPowerOfTwo.
