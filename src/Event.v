Require Core Memory.
Import Core Memory.

Section Events.
Context {contract_address precompile_params: Type}.

(** # Events

VM interfaces with two queues:

1. L2 [%events] events (see [%gs_events]),  emitted by [%OpEvent].
2. L1 [%l1_msg] events (see [%gs_l1_msgs]), emitted by [%OpToL1Message].

These queues are subject to rollbacks: in case of revert or panic, the
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

Definition l1_msg := event.

Record precompile_query := {
    q_tx_number_in_block: tx_num;
    q_shard_id: shard_id;
    q_contract_address: contract_address;
    q_key: precompile_params
}.

Inductive query :=
  | EventQuery : event -> query
  | L1MsgQuery : l1_msg -> query
  | PrecompileQuery : precompile_query -> query.


(* todo: probably these structures can be redesigned *)
End Events.
