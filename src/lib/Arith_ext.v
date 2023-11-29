Require Lia ZArith.

(** * Additional properties of natural numbers *)

Section PowerTwo.
  Import Coq.ZArith.Zpower.
  Import Coq.ZArith.BinIntDef.
  Import BinNums.


  Open Scope Z_scope.

  Theorem two_power_nat_0 :
    two_power_nat 0 = 1%Z.
  Proof.
    reflexivity.
  Qed.

  Theorem two_power_nat_gt_0:
    forall n : nat, BinInt.Z.gt (two_power_nat n) 0%Z.
  Proof.
    induction n.
    - rewrite two_power_nat_0.
      reflexivity.
    - rewrite two_power_nat_S.
      Lia.lia.
  Qed.


  (* Lemma two_power_nat_two_p: *)
  (*   forall x, two_power_nat x = two_p (Z.of_nat x). *)
  (* Proof. *)
  (*   induction x. auto. *)
  (*   rewrite two_power_nat_S. rewrite Nat2Z.inj_succ. rewrite two_p_S. Lia.lia. Lia.lia. *)
  (* Qed. *)
End PowerTwo.
