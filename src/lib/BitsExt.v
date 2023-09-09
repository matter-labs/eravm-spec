From mathcomp Require Import ssreflect eqtype seq tuple ssrbool.

From Bits Require Import spec bits tuple nat.
From EraVM Require Arith.

Import ssreflect.eqtype ssreflect.tuple Arith.

Lemma low_val n m b: val (@low n m b) = take m (val b).
elim: m n b.
- by intros; rewrite take0.
- move => //= n H n0 b.
  case /tupleP: b => x t //=.
  rewrite theadE.
  f_equal. by rewrite tuple.beheadCons.
Qed.

Lemma high_val n m b: val (@high n m b) = drop m (val b).
Proof.
    elim: m n b.
  - by intros; rewrite drop0.
  - move => //= n H n0 b.
    case /tupleP: b => x t //=.
    by rewrite tuple.beheadCons.
Qed.

Lemma val_catB n m (a:BITS n) (b:BITS m): val (a ## b) = b ++ a.
 Proof. by done. Qed.

 Lemma bits_size {n} (b:BITS n): size b = n.
   destruct b. simpl.
   pose proof (@eqP ssrnat.nat_eqType (size tval) n).
   inversion H; by [| rewrite i in H0].
 Qed.

 Ltac bits_subst_size:= repeat match goal with | [H : size ?x = _ |- context [size ?x]] => rewrite H end.
 Ltac bits_solve_size := rewrite !size_cat; bits_subst_size.
 Ltac bits_solve_subranges :=
   unfold subrange, subrange_len; apply /eqP; rewrite -val_eqE;
   repeat rewrite high_val; repeat rewrite low_val;
   repeat (rewrite take_cat; bits_solve_size; simpl);
   repeat (rewrite drop_cat; bits_solve_size; simpl);
     by repeat try do [rewrite !take0| rewrite! drop0 | rewrite! cats0 | rewrite! take_oversize| rewrite! take_size_cat | bits_subst_size].
