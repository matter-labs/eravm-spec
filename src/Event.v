From mathcomp Require ssreflect ssrfun ssrbool eqtype tuple zmodp.
Require Core memory.Depot TransientMemory.
Import Core memory.Depot TransientMemory.

Section Events.
  Import ssreflect ssreflect.tuple ssreflect.eqtype ssrbool.

  Context {contract_address precompile_params: eqType}.

  (** # Events

VM interfaces with two queues:

1. L1 [%l1_msg] events (see [%gs_l1_msgs]), emitted by [%OpToL1Message].
2. L2 [%events] events (see [%gs_events]),  emitted by [%OpEvent].

These queues are subject to [%rollback]s: in case of revert or panic, the
events emitted during the function or contract execution are rolled back.
   *)
  Record event := {
      ev_shard_id: shard_id;
      ev_is_first: bool;
      ev_tx_number_in_block: tx_num;
      ev_address: contract_address;
      ev_key: word;
      ev_value: word;
    }.


  (* begin details: equality on events *)
  Definition ev_eqn (x y:event) : bool :=
    match x,y with
    | Build_event ev_shard_id1 ev_is_first1 ev_tx_number_in_block1 ev_address1 ev_key1 ev_value1 ,
      Build_event ev_shard_id2 ev_is_first2 ev_tx_number_in_block2 ev_address2 ev_key2 ev_value2 =>
        (ev_shard_id1 == ev_shard_id2 ) &&
          (ev_is_first1 == ev_is_first2) &&
          (ev_tx_number_in_block1 == ev_tx_number_in_block2) &&
          (ev_address1 == ev_address2) &&
          (ev_key1 == ev_key2) &&
          (ev_value1 == ev_value2)
    end.

  Lemma ev_eqnP : Equality.axiom ev_eqn.
  Proof.
    move => [a b c d e g] [a' b' c' d' e' g'].
    simpl.
    Local Ltac orelse H := try rewrite! Bool.andb_false_r; try rewrite H; constructor; injection; intros; subst; by rewrite eq_refl in H.
    destruct (a == a') eqn: H1; [move: (eqP H1) => -> | by orelse H1].
    destruct (b == b') eqn: H2; [move: (eqP H2) => -> | by orelse H2].
    destruct (c == c') eqn: H3; [move: (eqP H3) => -> | by orelse H3].
    destruct (d == d') eqn: H4; [move: (eqP H4) => -> | by orelse H4].
    destruct (e == e') eqn: H5; [move: (eqP H5) => -> | by orelse H5].
    destruct (g == g') eqn: H6; [move: (eqP H6) => -> | by orelse H6].
    by rewrite eq_refl; constructor.
  Qed.

  Canonical ev_eqMixin := EqMixin ev_eqnP.
  Canonical ev_eqType := Eval hnf in EqType _ ev_eqMixin.
  (* end details *)

  Definition l1_msg := event.

  Record precompile_query := {
      q_tx_number_in_block: tx_num;
      q_shard_id: shard_id;
      q_contract_address: contract_address;
      q_key: precompile_params
    }.

  (* begin details: equality on precompile queries *)
  Definition pq_eqn (x y:precompile_query) : bool :=
    match x,y with
    | Build_precompile_query q_tx_number_in_block1 q_shard_id1 q_contract_address1 q_key1,
      Build_precompile_query q_tx_number_in_block2 q_shard_id2 q_contract_address2 q_key2 =>
        (q_tx_number_in_block1 == q_tx_number_in_block2) &&
          (q_shard_id1 == q_shard_id2) &&
          (q_contract_address1 == q_contract_address2)&&
          (q_key1 == q_key2)
    end .

  Lemma pq_eqnP : Equality.axiom pq_eqn.
  Proof.
    move => [a b c d] [a' b' c' d'] =>//=.
    destruct (a == a') eqn: H1; move: H1; last by constructor; injection; intros; subst; move: H1; rewrite eq_refl.
    move /eqP => -> //=.
    destruct (b == b') eqn: H2; [| by rewrite H2; constructor; injection; intros; subst; rewrite eq_refl in H2].
    destruct (c == c') eqn: H3; [| by rewrite ! Bool.andb_false_r; constructor; injection; intros; subst; rewrite eq_refl in H3].
    destruct (d == d') eqn: H4; [| by rewrite ! Bool.andb_false_r; constructor; injection; intros; subst; rewrite eq_refl in H4].
    move: H2 (eqP H2) => -> -> //=. constructor.
    by rewrite (eqP H3) (eqP H4).
  Qed.

  Canonical pq_eqMixin := EqMixin pq_eqnP.
  Canonical pq_eqType := Eval hnf in EqType _ pq_eqMixin.

  (* end details *)

  Inductive query :=
  | EventQuery : event -> query
  | L1MsgQuery : l1_msg -> query
  | PrecompileQuery : precompile_query -> query.

  (* begin details: equality on queries *)

  Definition query_eqn (x y: query) : bool :=
    match x,y with
    | EventQuery x, EventQuery y => x == y
    | L1MsgQuery x, L1MsgQuery y => x == y
    | PrecompileQuery x, PrecompileQuery y => x == y
    | _,_ => false
    end.

  Lemma query_eqnP : Equality.axiom query_eqn.
  Proof.
    unfold query_eqn.
    move => x y.
    destruct x, y =>//; try  destruct (_ == _) eqn: Heq; try (by done); constructor; try move /eqP in Heq; by [subst|injection].
  Qed.

  Canonical query_eqMixin := EqMixin query_eqnP.
  Canonical query_eqType := Eval hnf in EqType _ query_eqMixin.
  (* end details *)
  (* todo: probably these structures can be redesigned *)
End Events.
