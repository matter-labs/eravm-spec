Require Memory External.
Import Common Memory External.



(* For later: probably these structures can be redesigned so that *)

Record event := {
    ev_shard_id: shard_id;
    ev_is_first: bool;
    ev_tx_number_in_block: tx_num;
    ev_address: contract_address;
    ev_key: word;
    ev_value: word;
}.


Record precompile_query := {
    q_timestamp: timestamp;
    q_tx_number_in_block: tx_num;
    q_shard_id: shard_id;
    q_contract_address: contract_address;
    q_key: word;
    q_is_service: bool; (* is first message? *)
}.

Inductive query :=
  (* | StorageQuery : query *)
  | EventQuery : event -> query
  (* | L1MsgQuery : event -> query *)
  | PrecompileQuery : precompile_query -> query.

         
