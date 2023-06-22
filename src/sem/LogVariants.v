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
  forall flags pages xstack regs (arg_key: in_reg) (arg_dest_value: out_reg)
    new_regs new_pages read_value key (s1 s2:state),
    resolve_load_word xstack (regs,pages) arg_key key ->

    let fqa_storage := mk_fqa_key (current_storage_fqa xstack) key in
     
    storage_read (gs_revertable s1).(gs_depot) fqa_storage read_value ->
    resolve_store xstack (regs, pages) arg_dest_value (IntValue read_value) (new_regs, new_pages) ->
    step_xstate
      {|
           gs_regs         := regs;
           gs_pages        := pages;
           gs_callstack    := xstack;
           gs_flags        := flags;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;

           gs_callstack    := xstack;
           gs_flags        := flags;
           
         |} s1 s2 ->
    step (OpSLoad arg_key arg_dest_value) s1 s2

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
           gs_xstate := {|
           gs_regs         := regs;
           gs_pages        := pages;
           gs_callstack    := xstack;
           gs_flags        := flags;
                       |};
           gs_global       := gs;

           
           gs_context_u128 := context_u128;
         |}
         {|
           gs_xstate := {|
                         gs_regs         := new_regs;
                         gs_pages        := new_pages;
                         gs_callstack    := new_xstack;
                         gs_flags        := flags;
                       |};
           gs_global       := new_gs;

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
           gs_xstate := {|
                         gs_regs         := regs;
                         gs_pages        := pages;
                         gs_callstack    := xstack;

                         gs_flags        := flags;
                         |};
           
           gs_global       := gs;
           gs_context_u128 := context_u128;
         |}
         {|
           gs_xstate := {|
                         gs_regs         := new_regs;
                         gs_pages        := new_pages;
                         gs_callstack    := new_xstack;

                         gs_flags        := flags;
                       |};
           
           gs_global       := new_gs;
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
           gs_xstate := {|
                         gs_regs         := regs;
                         gs_pages        := pages;
                         gs_callstack    := xstack;
                         gs_flags        := flags;
                         
                       |};
           gs_global       := gs;

           gs_context_u128 := context_u128;
         |}
         {|
           gs_xstate := {|
                         gs_regs         := new_regs;
                         gs_pages        := new_pages;
                         
                         gs_callstack    := xstack;
                         gs_flags        := flags;
                       |};
           
           gs_global       := new_gs;


           gs_context_u128 := context_u128;
         |}

.

(* (* FIX: if not affordable then write 0 *) *)
(* | step_PrecompileCall: *)
(*   forall flags pages xstack context_u128 regs (arg_params arg_extra_ergs: in_reg) (arg_dest: out_reg) is_first *)
(*     new_regs new_pages params extra_ergs value gs new_gs, *)
    
(*     resolve_load_words xstack (regs, pages) [ *)
(*         (InReg arg_params, params); *)
(*         (InReg arg_extra_ergs, extra_ergs) *)
(*       ] -> *)

(*     PrecompileParameters.ABI.(decode)  *)
(*    emit_event (PrecompileQuery {| *)
(*                    ev_shard_id := current_shard xstack; *)
(*                    ev_is_first := is_first; *)
(*                    ev_tx_number_in_block := gs_tx_number_in_block gs; *)
(*                    ev_address := current_contract xstack; *)
(*                    ev_key := key; *)
(*                    ev_value := value; *)
(*                  |}) gs new_gs -> *)

   
   
(*     pay (extra_ergs ) xstack new_xstack-> *)
(*     step (OpPrecompileCall arg_key arg_extra_ergs arg_dest) *)
(*          {| *)
(*            gs_regs         := regs; *)
(*            gs_pages        := pages; *)
(*            gs_global       := gs; *)
(*            gs_callstack    := xstack; *)
(*            gs_flags        := flags; *)
(*            gs_context_u128 := context_u128; *)
(*          |} *)
(*          {| *)
(*            gs_regs         := new_regs; *)
(*            gs_pages        := new_pages; *)
(*            gs_global       := new_gs; *)


(*            gs_callstack    := xstack; *)
(*            gs_flags        := flags; *)
(*            gs_context_u128 := context_u128; *)
(*          |} *)
         

(* . *)

(* (*      | OpPrecompileCall _ _ => *) *)
(*  (* // add extra information about precompile abi in the "key" field *)

(*                 if not_enough_power { *)
(*                     // we have to update register *)
(*                     vm_state.perform_dst0_update( *)
(*                         vm_state.local_state.monotonic_cycle_counter, *)
(*                         PrimitiveValue::empty(), *)
(*                         dst0_mem_location, *)
(*                         &self, *)
(*                     ); *)
(*                     return; *)
(*                 } *)

(*                 let precompile_abi = PrecompileCallABI::from_u256(src0); *)
(*                 let PrecompileCallABI { *)
(*                     input_memory_offset, *)
(*                     input_memory_length, *)
(*                     output_memory_offset, *)
(*                     output_memory_length, *)
(*                     per_precompile_interpreted, *)
(*                 } = precompile_abi; *)

(*                 // normal execution *)
(*                 vm_state *)
(*                     .local_state *)
(*                     .callstack *)
(*                     .get_current_stack_mut() *)
(*                     .ergs_remaining = ergs_remaining; *)
(*                 let memory_page_to_read = CallStackEntry::<N, E>::heap_page_from_base( *)
(*                     vm_state *)
(*                         .local_state *)
(*                         .callstack *)
(*                         .get_current_stack() *)
(*                         .base_memory_page, *)
(*                 ); *)
(*                 let memory_page_to_write = CallStackEntry::<N, E>::heap_page_from_base( *)
(*                     vm_state *)
(*                         .local_state *)
(*                         .callstack *)
(*                         .get_current_stack() *)
(*                         .base_memory_page, *)
(*                 ); *)

(*                 let timestamp_to_read = vm_state.timestamp_for_first_decommit_or_precompile_read(); *)
(*                 let timestamp_to_write = *)
(*                     vm_state.timestamp_for_second_decommit_or_precompile_write(); *)
(*                 assert!(timestamp_to_read.0 + 1 == timestamp_to_write.0); *)

(*                 let precompile_inner_abi = PrecompileCallInnerABI { *)
(*                     input_memory_offset, *)
(*                     input_memory_length, *)
(*                     output_memory_offset, *)
(*                     output_memory_length, *)
(*                     memory_page_to_read: memory_page_to_read.0, *)
(*                     memory_page_to_write: memory_page_to_write.0, *)
(*                     precompile_interpreted_data: per_precompile_interpreted, *)
(*                 }; *)
(*                 let precompile_inner_abi = precompile_inner_abi.to_u256(); *)

(*                 let query = LogQuery { *)
(*                     timestamp: timestamp_for_log, *)
(*                     tx_number_in_block, *)
(*                     aux_byte: PRECOMPILE_AUX_BYTE, *)
(*                     shard_id, *)
(*                     address, *)
(*                     key: precompile_inner_abi, *)
(*                     read_value: U256::zero(), *)
(*                     written_value: U256::zero(), *)
(*                     rw_flag: false, *)
(*                     rollback: false, *)
(*                     is_service: is_first_message, *)
(*                 }; *)
(*                 vm_state.call_precompile(vm_state.local_state.monotonic_cycle_counter, query); *)
(*                 vm_state.witness_tracer.add_sponge_marker( *)
(*                     vm_state.local_state.monotonic_cycle_counter, *)
(*                     SpongeExecutionMarker::StorageLogReadOnly, *)
(*                     1..4, *)
(*                     false, *)
(*                 ); *)
(*                 let result = PrimitiveValue { *)
(*                     value: U256::from(1u64), *)
(*                     is_pointer: false, *)
(*                 }; *)
(*                 vm_state.perform_dst0_update( *)
(*                     vm_state.local_state.monotonic_cycle_counter, *)
(*                     result, *)
(*                     dst0_mem_location, *)
(*                     &self, *)
(*                 ); *)
(* *) *)
