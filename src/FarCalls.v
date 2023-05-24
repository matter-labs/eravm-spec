From RecordUpdate Require Import RecordSet.
Require Common Ergs Condition ExecutionStack Memory Instruction State MemoryOps ABI SemanticCommon.

Import Bool ZArith Common CodeStorage Condition Ergs ExecutionStack MemoryBase Memory MemoryOps
  Instruction State SemanticCommon ZMod
  ABI ABI.FarCall ABI.Ret ABI.NearCall ABI.FatPointer Arg Arg.Coercions RecordSetNotations.
Import List ListNotations.

Definition INITIAL_SP_ON_FAR_CALL : stack_address := ZMod.int_mod_of _ 1024.
Definition NEW_FRAME_MEMORY_STIPEND : mem_address := ZMod.int_mod_of _ 1024.

Record FarCallExceptions : Set := {
    fce_input_is_not_pointer_when_expected : bool;
    fce_invalid_code_hash_format : bool;
    fce_not_enough_ergs_to_decommit : bool;
    fce_not_enough_ergs_to_grow_memory : bool;
    fce_malformed_abi_quasi_pointer : bool;
    fce_call_in_now_constructed_system_contract : bool;
    fce_note_enough_ergs_for_extra_far_call_costs : bool;
  }.

Definition code_storage := code_storage _ instruction_invalid.
Definition code_manager := code_manager.

Inductive decommitment_cost (cm:code_manager) vhash (code_length_in_words: code_length): ergs -> Prop :=
  |dc_fresh: forall cost,
    is_fresh _ _ cm vhash = true->
    (cost, false) = Ergs.ERGS_PER_CODE_WORD_DECOMMITTMENT * (resize _ _ code_length_in_words) ->
    decommitment_cost cm vhash code_length_in_words cost
  |dc_not_fresh:
    is_fresh _ _ cm vhash = false ->
    decommitment_cost cm vhash code_length_in_words zero32.

Inductive alloc_pages_extframe:  pages -> active_pages -> code_page -> pages * active_pages -> Prop :=
  | ape_alloc: forall code mm ctx code_id const_id stack_id heap_id heap_aux_id,
      alloc_pages_extframe mm ctx code
     ( (heap_aux_id, (DataPage _ _ (empty _)))::
        (heap_id, (DataPage _ _ (empty _)))::
        (stack_id, (StackPage _ _ (empty _)))::
        (const_id,(ConstPage _ _ (empty _)))::
        (code_id,(CodePage _ _ code))::mm,
       {|
         ctx_code_page_id := code_id;
         ctx_const_page_id := const_id;
         ctx_stack_page_id := stack_id;
         ctx_heap_page_id := heap_id;
         ctx_auxheap_page_id := heap_aux_id;
         ctx_heap_bound := NEW_FRAME_MEMORY_STIPEND;
         ctx_aux_heap_bound := NEW_FRAME_MEMORY_STIPEND;
       |} ).

Inductive grow_page: forward_page_type -> mem_address -> active_pages -> active_pages -> Prop :=
  | gp_heap: forall code_id const_id stack_id heap_id heap_aux_id heap_bound
               aux_heap_bound new_bound diff,
      heap_bound + diff = (new_bound, false) ->
      grow_page UseHeap diff
      {|
         ctx_code_page_id := code_id;
         ctx_const_page_id := const_id;
         ctx_stack_page_id := stack_id;
         ctx_heap_page_id := heap_id;
         ctx_auxheap_page_id := heap_aux_id;
         ctx_heap_bound := heap_bound;
         ctx_aux_heap_bound := aux_heap_bound;
       |}
      {|
         ctx_code_page_id := code_id;
         ctx_const_page_id := const_id;
         ctx_stack_page_id := stack_id;
         ctx_heap_page_id := heap_id;
         ctx_auxheap_page_id := heap_aux_id;
         ctx_heap_bound := new_bound;
         ctx_aux_heap_bound := aux_heap_bound;
       |}
  | gp_aux_heap: forall code_id const_id stack_id heap_id heap_aux_id heap_bound
                   aux_heap_bound new_bound diff,
      aux_heap_bound + diff = (new_bound, false) ->
      grow_page UseAuxHeap diff
      {|
         ctx_code_page_id := code_id;
         ctx_const_page_id := const_id;
         ctx_stack_page_id := stack_id;
         ctx_heap_page_id := heap_id;
         ctx_auxheap_page_id := heap_aux_id;
         ctx_heap_bound := heap_bound;
         ctx_aux_heap_bound := aux_heap_bound;
       |}
      {|
         ctx_code_page_id := code_id;
         ctx_const_page_id := const_id;
         ctx_stack_page_id := stack_id;
         ctx_heap_page_id := heap_id;
         ctx_auxheap_page_id := heap_aux_id;
         ctx_heap_bound := heap_bound;
         ctx_aux_heap_bound := new_bound;
       |}.

Inductive code_fetch_and_pay : depot -> code_manager -> contract_address
                               -> execution_stack -> execution_stack * code_page
                               ->Prop :=
| cfp_apply:
  forall depot codes (dest_addr: contract_address) vhash dest_addr new_code_page code_length
    cost__decomm xstack0 xstack1,
    code_fetch _ _ depot codes.(cm_storage _ _) dest_addr (vhash, new_code_page, code_length) ->
    decommitment_cost codes vhash code_length cost__decomm ->
    pay cost__decomm xstack0 xstack1 ->
    code_fetch_and_pay depot codes dest_addr xstack0 (xstack1, new_code_page).

Definition max_passable (remaining:ergs) : ergs :=
    int_mod_of _(((int_val _ remaining) / 64 ) * 63)%Z.

Inductive pass_allowed_ergs : ergs -> ergs -> execution_stack -> execution_stack -> Prop :=
  | pae_apply: forall xstack1 xstack2 pass_ergs_query,
  let pass_ergs_actual := ZMod.min _ (max_passable (ergs_remaining xstack1)) pass_ergs_query in
  pay pass_ergs_actual xstack1 xstack2 ->
  pass_allowed_ergs pass_ergs_query pass_ergs_actual xstack1 xstack2.



(* Not implemented: shards *)
Inductive step_farcall: instruction -> state -> state -> Prop :=

|step_FarCall_NonKernel_Forward: forall flags regs pages xstack0 xstack1 xstack2
                                   (handler:imm_in) handler_location depot
                                   codes context_u128 (abi dest:in_reg)
                                   is_static new_pages
                                   new_code_page (dest_val:word_type)
                                   abi_val
                                   new_mem_ctx in_ptr shrunk_ptr shard_id
                                   pass_ergs_query pass_ergs_actual vtag,

    let old_extframe := topmost_extframe xstack0 in
    let old_mem_ctx  := old_extframe.(ecf_pages) in
    let current_contract := old_extframe.(ecf_this_address) in

    resolve_fetch_value regs xstack0 pages dest (mk_pv vtag dest_val) ->
    resolve_fetch_value regs xstack0 pages abi (PtrValue abi_val) ->
    resolve_fetch_value regs xstack0 pages handler (IntValue handler_location) ->
    let dest_addr := resize _ 160 dest_val in
    addr_is_kernel dest_addr = false ->

    FarCall.ABI.(decode) abi_val = Some
                                     {|
                                       fc_memory_quasi_fat_ptr := in_ptr;
                                       fc_ergs_passed          := pass_ergs_query;
                                       fc_shard_id             := shard_id;
                                       fc_forwarding_mode      := ForwardFatPointer;
                                       fc_constructor_call     := false;
                                       fc_to_system            := false;
                                     |} ->

    fat_ptr_shrink in_ptr shrunk_ptr ->

    code_fetch_and_pay depot codes dest_addr xstack0 (xstack1, new_code_page) ->

    alloc_pages_extframe pages old_mem_ctx new_code_page (new_pages, new_mem_ctx) ->

    pass_allowed_ergs pass_ergs_query pass_ergs_actual xstack1 xstack2 ->

    let encoded_shrunk_ptr := FatPointer.ABI.(encode) shrunk_ptr in
    let new_regs := regs_state_zero <| gprs_r1 := PtrValue encoded_shrunk_ptr |> in
    let new_stack := ExternalCall {|
                         ecf_this_address := dest_addr;
                         ecf_msg_sender := current_contract;
                         ecf_code_address := zero16;
                         ecf_pages := new_mem_ctx;
                         ecf_is_static :=  ecf_is_static old_extframe || is_static;
                         ecf_context_u128_value := context_u128;
                         ecf_saved_storage_state := load _ current_contract depot;
                         ecf_common := {|
                                        cf_exception_handler_location := resize _ code_address_bits handler_location;
                                        cf_sp := INITIAL_SP_ON_FAR_CALL;
                                        cf_pc := zero16;
                                        cf_ergs_remaining := pass_ergs_actual;
                                      |};
                       |} (Some xstack2) in
    step_farcall (OpFarCall abi dest handler is_static)
             {|
               gs_flags        := flags;
               gs_regs         := regs;
               gs_pages    := pages;
               gs_callstack    := xstack0;
               gs_context_u128 := context_u128;


               gs_depot     := depot;
               gs_contracts    := codes;
             |}
             {|
               gs_flags        := flags_clear;
               gs_regs         := new_regs;
               gs_pages    := new_pages;
               gs_callstack    := new_stack;
               gs_context_u128 := zero128;


               gs_depot        := depot;
               gs_contracts    := codes;
             |}


|step_FarCall_NonKernel_HeapOrAuxHeap:
  forall flags regs pages xstack0 xstack1 xstack2 
                                   (handler:imm_in) handler_location depot
                                   codes context_u128 (abi dest:in_reg)
                                   is_static new_pages
                                   new_code_page (dest_val:word_type)
                                   abi_val
                                   new_mem_ctx in_ptr shard_id
                                   pass_ergs_query vtag
                                   fwd_mode page_id current_bound diff
                                   new_caller_mem_ctx new_caller_stack
                                   pass_ergs_actual ,

    let old_extframe := topmost_extframe xstack0 in
    let old_mem_ctx  := old_extframe.(ecf_pages) in
    let current_contract := old_extframe.(ecf_this_address) in
    resolve_fetch_value regs xstack0 pages dest (mk_pv vtag dest_val) ->
    resolve_fetch_value regs xstack0 pages abi (PtrValue abi_val) ->
    resolve_fetch_value regs xstack0 pages handler (IntValue handler_location) ->
    let dest_addr := resize _ 160 dest_val in

    addr_is_kernel dest_addr = false ->

    FarCall.ABI.(decode) abi_val = Some
                                     {|
                                       fc_memory_quasi_fat_ptr := in_ptr;
                                       fc_ergs_passed          := pass_ergs_query;
                                       fc_shard_id             := shard_id;
                                       fc_forwarding_mode      := fwd_mode;
                                       fc_constructor_call     := false;
                                       fc_to_system            := false;
                                     |} ->
    (fwd_mode = UseHeap \/ fwd_mode = UseAuxHeap) ->
    validate_fresh in_ptr = no_exceptions ->
    select_page_bound xstack0 fwd_mode (page_id, current_bound) ->
    code_fetch_and_pay depot codes dest_addr xstack0 (xstack1, new_code_page) ->

    alloc_pages_extframe pages old_extframe.(ecf_pages) new_code_page (new_pages, new_mem_ctx) ->

    fat_ptr_induced_growth in_ptr current_bound diff ->
    pay (Ergs.growth_cost diff) xstack1 xstack2 ->

    grow_page fwd_mode diff old_mem_ctx new_caller_mem_ctx ->
    let xstack3 := update_memory_context new_caller_mem_ctx xstack2 in

    pass_allowed_ergs pass_ergs_query pass_ergs_actual xstack3 new_caller_stack ->

    let out_ptr := in_ptr <| fp_page := page_id |> in
    let new_regs := regs_state_zero <| gprs_r1 := PtrValue (FatPointer.ABI.(encode) out_ptr) |> in
    let new_xstack := ExternalCall {|
                      ecf_this_address := dest_addr;
                      ecf_msg_sender := current_contract;
                      ecf_code_address := zero16;
                      ecf_pages       := new_mem_ctx;
                      ecf_is_static :=  ecf_is_static old_extframe || is_static;
                      ecf_context_u128_value := context_u128;
                      ecf_saved_storage_state := load _ current_contract depot;
                      ecf_common := {|
                                     cf_exception_handler_location := resize _ _ handler_location;
                                     cf_sp := INITIAL_SP_ON_FAR_CALL;
                                     cf_pc := zero16;
                                     cf_ergs_remaining := pass_ergs_actual;
                                   |};

                    |} (Some new_caller_stack) in
    step_farcall (OpFarCall abi dest handler is_static)
             {|
               gs_flags        := flags;
               gs_regs         := regs;
               gs_pages    := pages;
               gs_callstack    := xstack0;
               gs_context_u128 := context_u128;


               gs_depot    := depot;
               gs_contracts    := codes;
             |}
             {|
               gs_flags        := flags_clear;
               gs_regs         := new_regs;
               gs_pages    := new_pages;
               gs_callstack    := new_xstack;
               gs_context_u128 := zero128;


               gs_depot     := depot;
               gs_contracts    := codes;
             |}

|step_FarCall_Kernel_Forward: forall flags regs pages xstack0 xstack1 xstack2
                                   (handler:imm_in) handler_location depot
                                   codes context_u128 (abi dest:in_reg)
                                   is_static new_pages
                                   new_code_page (dest_val:word_type)
                                   abi_val
                                   new_mem_ctx in_ptr shrunk_ptr shard_id
                                   pass_ergs_query pass_ergs_actual vtag,

    let old_extframe := topmost_extframe xstack0 in
    let old_mem_ctx  := old_extframe.(ecf_pages) in
    let current_contract := old_extframe.(ecf_this_address) in

    resolve_fetch_value regs xstack0 pages dest (mk_pv vtag dest_val) ->
    resolve_fetch_value regs xstack0 pages abi (PtrValue abi_val) ->
    resolve_fetch_value regs xstack0 pages handler (IntValue handler_location) ->
    let dest_addr := resize _ 160 dest_val in
    addr_is_kernel dest_addr = true ->
    
    FarCall.ABI.(decode) abi_val = Some
                                     {|
                                       fc_memory_quasi_fat_ptr := in_ptr;
                                       fc_ergs_passed := pass_ergs_query;
                                       fc_shard_id := shard_id;
                                       fc_forwarding_mode := ForwardFatPointer;
                                       fc_constructor_call := false;
                                       fc_to_system := true;
                                     |} ->

    fat_ptr_shrink in_ptr shrunk_ptr ->

    code_fetch_and_pay depot codes dest_addr xstack0 (xstack1, new_code_page) ->

    alloc_pages_extframe pages old_mem_ctx new_code_page (new_pages, new_mem_ctx) ->

    pass_allowed_ergs pass_ergs_query pass_ergs_actual xstack1 xstack2 ->

    let encoded_shrunk_ptr := FatPointer.ABI.(encode) shrunk_ptr in
    let new_regs := regs_state_zero <| gprs_r1 := PtrValue encoded_shrunk_ptr |> in
    let new_stack := ExternalCall {|
                         ecf_this_address := dest_addr;
                         ecf_msg_sender := current_contract;
                         ecf_code_address := zero16;
                         ecf_pages       := new_mem_ctx;
                         ecf_is_static :=  ecf_is_static old_extframe || is_static;
                         ecf_context_u128_value := context_u128;
                         ecf_saved_storage_state := load _ current_contract depot;
                         ecf_common := {|
                                        cf_exception_handler_location
                                        := resize _ code_address_bits handler_location;
                                        cf_sp := INITIAL_SP_ON_FAR_CALL;
                                        cf_pc := zero16;
                                        cf_ergs_remaining := pass_ergs_actual;
                                      |};
                       |} (Some xstack2) in
    step_farcall (OpFarCall abi dest handler is_static)
             {|
               gs_flags        := flags;
               gs_regs         := regs;
               gs_pages    := pages;
               gs_callstack    := xstack0;
               gs_context_u128 := context_u128;


               gs_depot     := depot;
               gs_contracts    := codes;
             |}
             {|
               gs_flags        := flags_clear;
               gs_regs         := new_regs;
               gs_pages        := new_pages;
               gs_callstack    := new_stack;
               gs_context_u128 := zero128;


               gs_depot        := depot;
               gs_contracts    := codes;
             |}


.
