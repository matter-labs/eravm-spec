From Coq.Logic    Require Decidable.

Import Decidable.

Section Decidability.

  Definition dec(A: Prop) := { A } + { ~ A }.

  Lemma dec_decidable :
    forall P, dec P -> decidable P.
  Proof. unfold dec, decidable. intros ? []; tauto. Qed.


  Theorem dec_conj:
    forall A B: Prop,
      dec A ->
      dec B ->
      dec (A /\ B).
  Proof. unfold dec. intros; tauto. Qed.

  Theorem dec_not : forall A:Prop, dec A -> dec (~ A).
  Proof. unfold dec. tauto. Qed.

  Theorem dec_not_not : forall P:Prop, dec P -> ~ ~ P -> P.
  Proof. unfold dec; tauto. Qed.

  Theorem not_not : forall P: Prop,
      dec P -> ~ ~ P -> P.
  Proof. unfold dec; tauto. Qed.

  Theorem dec_or:
    forall A B: Prop,
      dec A ->
      dec B ->
      dec (A \/ B).
  Proof. unfold dec; intros; tauto. Qed.

  Definition eq_dec (T:Type) := forall x1 x2: T, dec (x1 = x2).

End Decidability.

Ltac decide_equality :=
  unfold eq_dec, dec in *;
  repeat decide equality;
  unfold eq_dec, dec in *;
  eauto with decidable_prop.
