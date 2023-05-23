From RecordUpdate Require Import RecordSet.
Require Common Condition Memory Instruction State MemoryOps ABI SemanticCommon.

Import Bool ZArith Common CodeStorage Condition MemoryBase Memory MemoryOps
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

Definition max_passable (remaining:ergs) : ergs :=
    int_mod_of _(((int_val _ remaining) / 64 ) * 63)%Z.

Inductive decommitment_cost (cm:code_manager _ instruction_invalid) vhash (code_length_in_words: code_length): ergs -> Prop :=
  |dc_fresh: forall cost,
    is_fresh _ _ cm vhash = true->
    (cost, false) = Ergs.ERGS_PER_CODE_WORD_DECOMMITTMENT * (resize _ _ code_length_in_words) ->
    decommitment_cost cm vhash code_length_in_words cost
  |dc_not_fresh:
    is_fresh _ _ cm vhash = false ->
    decommitment_cost cm vhash code_length_in_words zero32.



Inductive alloc_pages_extframe:  mem_manager -> ctx_mem_pages -> code_page -> mem_manager * ctx_mem_pages -> Prop :=
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
         ctx_heap_aux_page_id := heap_aux_id;
         ctx_heap_bound := NEW_FRAME_MEMORY_STIPEND;
         ctx_aux_heap_bound := NEW_FRAME_MEMORY_STIPEND;
       |} ).

Inductive step_farcall: instruction -> global_state -> global_state -> Prop :=

|step_FarCall_NonKernel_Forward: forall flags regs mem_pages xstack0 xstack1 xstack2 (handler:imm_in) handler_location contracts codes context_u128 (abi dest:in_reg) is_static new_mem_pages new_xstack new_code_page code_length dest_val abi_val new_mem_ctx in_ptr shrunk_ptr shard_id pass_ergs_query cost__decomm vhash,

    let old_frame := topmost_extframe xstack0 in
    resolve_fetch_value regs xstack0 mem_pages dest (IntValue dest_val) -> (* Fixme: also allow pointers *)
    resolve_fetch_value regs xstack0 mem_pages abi (PtrValue abi_val) ->
    resolve_fetch_value regs xstack0 mem_pages handler (IntValue handler_location) ->

    (* any shard ID is accepted atm; consider_new_tx is ignored. *)
    FarCall.ABI.(decode) abi_val = Some (FarCall.mk_params in_ptr pass_ergs_query shard_id ForwardFatPointer false false) ->

    fat_ptr_shrink in_ptr shrunk_ptr ->


    code_fetch _ _ contracts codes.(cm_storage _ _) (resize 256 _ dest_val) (vhash, new_code_page, code_length) ->
    alloc_pages_extframe mem_pages old_frame.(ecf_mem_context) new_code_page (new_mem_pages, new_mem_ctx) ->

    decommitment_cost codes vhash code_length cost__decomm ->
    pay cost__decomm xstack0 xstack1 ->

    let actual_pass_ergs := ZMod.min _ (max_passable (ergs_remaining xstack1)) pass_ergs_query in
    pay actual_pass_ergs xstack1 xstack2 ->

    let active_storage := load contracts_params old_frame.(ecf_this_address) contracts in
    let encoded_shrunk_ptr := FatPointer.ABI.(encode) shrunk_ptr in
    let new_regs := regs_state_zero <| gprs_r1 := PtrValue encoded_shrunk_ptr |> in
    let new_frame := {|
                      ecf_this_address := resize _ _ dest_val;
                      ecf_msg_sender := old_frame.(ecf_this_address);
                      ecf_code_address := resize _ _ dest_val;
                      ecf_mem_context := new_mem_ctx;
                      ecf_is_static :=  ecf_is_static old_frame || is_static;
                      ecf_context_u128_value := context_u128;
                      ecf_saved_storage_state := active_storage;
                      ecx_common := {|
                                     cf_exception_handler_location := resize _ _ handler_location;
                                     cf_sp := INITIAL_SP_ON_FAR_CALL;
                                     cf_pc := zero16;
                                     cf_ergs_remaining := actual_pass_ergs;
                                   |};

                    |} in
    step_farcall (OpFarCall abi dest handler is_static)
             {|
               gs_flags        := flags;
               gs_regs         := regs;
               gs_mem_pages    := mem_pages;
               gs_callstack    := xstack0;
               gs_context_u128 := context_u128;


               gs_contracts    := contracts;
               gs_contract_code:= codes;
             |}
             {|
               gs_flags        := flags_clear;
               gs_regs         := new_regs;
               gs_mem_pages    := new_mem_pages;
               gs_callstack    := new_xstack;
               gs_context_u128 := zero128;


               gs_contracts    := contracts;
               gs_contract_code:= codes;
             |}
.
