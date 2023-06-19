From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Condition Ergs CallStack Event Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations MetaParameters.
Import ZArith List ListNotations.

Definition is_rollup (xstack: callstack) : bool := zero8 == current_shard xstack.

Definition net_pubdata xstack : Z := if is_rollup xstack then INITIAL_STORAGE_WRITE_PUBDATA_BYTES else 0.
    
Definition current_storage_fqa (xstack:callstack) : fqa_storage :=
  mk_fqa_storage (current_shard xstack) (current_contract xstack).


Inductive step: instruction -> smallstep :=

| step_SLoad:
  forall gs flags pages xstack context_u128 regs (arg_key: in_reg) (arg_dest_value: out_reg)
    new_regs new_pages read_value key,
    resolve_load_word xstack (regs,pages) arg_key key ->

    let fqa_storage := mk_fqa_key (current_storage_fqa xstack) key in
     
    storage_read gs.(gs_revertable).(gs_depot) fqa_storage read_value ->
    resolve_store xstack (regs, pages) arg_dest_value (IntValue read_value) (new_regs, new_pages) ->
    step (OpSLoad arg_key arg_dest_value)
         {|
           gs_regs         := regs;
           gs_pages        := pages;
           gs_callstack    := xstack;
           gs_flags        := flags;
           
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;


           gs_callstack    := xstack;
           gs_flags        := flags;
           
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}

| step_SStore:
  forall flags pages xstack context_u128 regs (arg_key: in_reg) (arg_dest_value: out_reg)
    new_regs new_pages new_xstack key new_depot write_value gs new_gs,
    resolve_load_word xstack (regs,pages) arg_key key ->

    (* there are currently no refunds *)
    let fqa_storage := mk_fqa_key (current_storage_fqa xstack) key in
    let old_depot := gs.(gs_revertable).(gs_depot) in
    storage_write old_depot fqa_storage write_value new_depot ->
    global_state_new_depot new_depot gs new_gs ->


    pay (ergs_of (net_pubdata xstack)) xstack new_xstack ->
    
    resolve_store xstack (regs, pages) arg_dest_value (IntValue write_value) (new_regs, new_pages) ->
    
    step (OpSLoad arg_key arg_dest_value)
         {|
           gs_regs         := regs;
           gs_pages        := pages;
           gs_global       := gs;
           gs_callstack    := xstack;

           
           gs_flags        := flags;
           gs_context_u128 := context_u128;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;
           gs_global       := new_gs;
           gs_callstack    := new_xstack;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
         |}

| step_ToL1:
  forall flags pages xstack new_xstack context_u128 regs (arg_key: in_reg) (arg_value: in_reg) _tagk _tagv is_first 
    new_regs new_pages key value gs new_gs cost,
    resolve_loads xstack (regs, pages) [
        (InReg arg_key, mk_pv _tagk key);
        (InReg arg_value, mk_pv _tagv value)
      ] ->

    (cost, false) = gs_current_ergs_per_pubdata_byte gs * ergs_of L1_MESSAGE_PUBDATA_BYTES ->
    pay cost xstack new_xstack ->

    emit_l1_msg {|
        ev_shard_id := current_shard xstack;
        ev_is_first := is_first;
        ev_tx_number_in_block := gs_tx_number_in_block gs;
        ev_address := current_contract xstack;
        ev_key := key;
        ev_value := value;
      |} gs new_gs ->
    
    step (OpToL1Message arg_key arg_value is_first)
         {|
           gs_regs         := regs;
           gs_pages        := pages;
           gs_global       := gs;
           gs_callstack    := xstack;
           
           gs_flags        := flags;
           gs_context_u128 := context_u128;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;
           gs_global       := new_gs;
           gs_callstack    := new_xstack;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
         |}
         
| step_Event:
  forall flags pages xstack context_u128 regs (arg_key: in_reg) (arg_value: in_reg) is_first
    new_regs new_pages key value gs new_gs,
    resolve_load_words xstack (regs, pages) [
        (InReg arg_key, key);
        (InReg arg_value, value)
      ] ->

   emit_event (EventQuery {|
                   ev_shard_id := current_shard xstack;
                   ev_is_first := is_first;
                   ev_tx_number_in_block := gs_tx_number_in_block gs;
                   ev_address := current_contract xstack;
                   ev_key := key;
                   ev_value := value;
                 |}) gs new_gs ->
    
    
    step (OpEvent arg_key arg_value is_first)
         {|
           gs_regs         := regs;
           gs_pages        := pages;
           gs_global       := gs;
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_context_u128 := context_u128;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;
           gs_global       := new_gs;


           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_context_u128 := context_u128;
         |}

.

