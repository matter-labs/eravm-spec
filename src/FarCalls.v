From RecordUpdate Require Import RecordSet.
Require Common Ergs Condition ExecutionStack Memory Instruction State MemoryOps ABI SemanticCommon.

Import
BinIntDef.Z
Bool
List
ListNotations
ZArith
ZMod.


Import
ABI ABI.FarCall ABI.FatPointer ABI.NearCall ABI.Ret
CodeStorage
Common
Condition
Ergs
ExecutionStack
Memory
MemoryBase
MemoryOps
RecordSetNotations
SemanticCommon
State.

Import Instruction Arg Arg.Coercions.

Local Coercion Z.b2z: bool >-> Z.

Definition INITIAL_SP_ON_FAR_CALL : stack_address := ZMod.int_mod_of _ 1024.
Definition NEW_FRAME_MEMORY_STIPEND : mem_address := ZMod.int_mod_of _ 1024.
Definition max_passable (remaining:ergs) : ergs :=
  int_mod_of _(((int_val _ remaining) / 64 ) * 63)%Z.


Inductive decommitment_cost (cm:code_manager) vhash (code_length_in_words: code_length): ergs -> Prop :=
|dc_fresh: forall cost,
    is_fresh _ _ cm vhash = true->
    (cost, false) = Ergs.ERGS_PER_CODE_WORD_DECOMMITTMENT * (resize _ _ code_length_in_words) ->
    decommitment_cost cm vhash code_length_in_words cost
|dc_not_fresh:
  is_fresh _ _ cm vhash = false ->
  decommitment_cost cm vhash code_length_in_words zero32.

Inductive alloc_pages_extframe:  (pages * active_pages) -> code_page -> pages * active_pages -> Prop :=
| ape_alloc: forall code mm ctx code_id const_id stack_id heap_id heap_aux_id,
    alloc_pages_extframe (mm,ctx) code
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
          ctx_auxheap_bound := NEW_FRAME_MEMORY_STIPEND;
        |} ).

Inductive paid_code_fetch masking_allowed: depot -> code_manager -> contract_address
                               -> execution_stack -> execution_stack * code_page
                               ->Prop :=
| cfp_apply:
  forall depot codes (dest_addr: contract_address) vhash dest_addr new_code_page code_length
    cost__decomm xstack0 xstack1,

    code_fetch _ _ masking_allowed depot codes.(cm_storage _ _) dest_addr (vhash, new_code_page, code_length) ->
    decommitment_cost codes vhash code_length cost__decomm ->
    pay cost__decomm xstack0 xstack1 ->
    paid_code_fetch masking_allowed depot codes dest_addr xstack0 (xstack1, new_code_page).


Inductive pass_allowed_ergs : (ergs * execution_stack )-> ergs * execution_stack -> Prop :=
| pae_apply: forall xstack1 xstack2 pass_ergs_query,
    let pass_ergs_actual := ZMod.min _ (max_passable (ergs_remaining xstack1)) pass_ergs_query in
    pay pass_ergs_actual xstack1 xstack2 ->
    pass_allowed_ergs (pass_ergs_query,xstack1) (pass_ergs_actual, xstack2).


Inductive pay_heaps_growth_or_burn: forward_page_type -> fat_ptr -> execution_stack -> execution_stack -> Prop  :=
| mpgb_forward p xstack:
  pay_heaps_growth_or_burn ForwardFatPointer p xstack xstack

| mpgb_heap in_ptr xstack0 xstack1:
  pay_growth_or_burn_ptr (heap_bound xstack0) in_ptr xstack0 xstack1 ->
  pay_heaps_growth_or_burn UseHeap in_ptr xstack0 xstack1
| mpgb_auxheap in_ptr xstack0 xstack1:
  pay_growth_or_burn_ptr (auxheap_bound xstack0) in_ptr xstack0 xstack1 ->
  pay_heaps_growth_or_burn UseAuxHeap in_ptr xstack0 xstack1.

Inductive paid_forward: forward_page_type -> fat_ptr * execution_stack * active_pages  -> fat_ptr * execution_stack * active_pages -> Prop :=
|fcf_useheap: forall diff in_ptr xstack0 xstack1 old_apages grown_apages,
    let bound := heap_bound xstack0 in
    validate_fresh in_ptr = no_exceptions ->
    fat_ptr_induced_growth in_ptr bound diff ->
    pay_growth_or_burn diff xstack0 xstack1 ->
    grow_heap_page diff old_apages grown_apages ->
    paid_forward UseHeap (in_ptr, xstack0, old_apages) (in_ptr <| fp_page := active_heap_id xstack0 |>, xstack1, grown_apages)

|fcf_useauxheap: forall diff in_ptr xstack0 xstack1 old_apages grown_apages,
    let bound := auxheap_bound xstack0 in
    validate_fresh in_ptr = no_exceptions ->
    fat_ptr_induced_growth in_ptr bound diff ->
    pay_growth_or_burn diff xstack0 xstack1 ->
    grow_auxheap_page diff old_apages grown_apages ->
    paid_forward UseAuxHeap (in_ptr, xstack0, old_apages) (in_ptr <| fp_page := active_heap_id xstack0 |>, xstack1, grown_apages)

|fcf_forwardfatpointer: forall in_ptr xstack pages out_ptr,
    validate_non_fresh in_ptr = no_exceptions ->
    fat_ptr_shrink in_ptr out_ptr ->
    paid_forward ForwardFatPointer (in_ptr, xstack, pages) (out_ptr, xstack,pages)
.

Definition regs_effect regs (is_system is_ctor:bool) ptr :=
  let far_call_r2 :=
    let is_system_bit := shiftl is_system 1 in
    let is_ctor_bit := shiftl is_ctor 0 in
    IntValue (int_mod_of word_bits (Z.lor is_system_bit is_ctor_bit)) in
  let enc_ptr := FatPointer.ABI.(encode) ptr in
     if is_system then
       regs
       <| gprs_r1 := PtrValue enc_ptr |>
       <| gprs_r2 := far_call_r2      |>
       (* In system calls, preserve values in r3-r13 but clear ptr tags *)
       <| gprs_r3 ::= clear_pointer_tag |>
       <| gprs_r4 ::= clear_pointer_tag |>
       <| gprs_r5 ::= clear_pointer_tag |>
       <| gprs_r6 ::= clear_pointer_tag |>
       <| gprs_r7 ::= clear_pointer_tag |>
       <| gprs_r8 ::= clear_pointer_tag |>
       <| gprs_r9 ::= clear_pointer_tag |>
       <| gprs_r10 ::= clear_pointer_tag |>
       <| gprs_r11 ::= clear_pointer_tag |>
       <| gprs_r12 ::= clear_pointer_tag |>
       <| gprs_r13 ::= clear_pointer_tag |>
       (* zero the rest *)
       <| gprs_r14 := pv0 |>
       <| gprs_r15 := pv0 |>
     else
       regs_state_zero <| gprs_r1 := PtrValue enc_ptr |>.

Inductive farcall_type : Set := Normal | Mimic | Delegate.
Definition CALL_IMPLICIT_PARAMETER_REG := R3.

Definition select type (callers_caller caller dest: contract_address) (frame_ctx reg_ctx: u128) regs : (contract_address * contract_address * u128) :=
  match type with
  | Normal => (dest, caller, reg_ctx)
  | Delegate => (caller, callers_caller, frame_ctx)
  | Mimic =>
      let r3_value := (fetch_gpr regs CALL_IMPLICIT_PARAMETER_REG).(value) in
      (dest, resize _ _ r3_value, reg_ctx)
  end.

Definition select_this_address type (caller dest: contract_address) :=
  match type with
  | Normal => dest
  | Mimic => dest
  | Delegate => caller
  end.

Definition select_sender type (callers_caller caller : contract_address) regs :=
  match type with
  | Normal => caller
  | Delegate => callers_caller
  | Mimic =>
      let r3_value := (fetch_gpr regs CALL_IMPLICIT_PARAMETER_REG).(value) in
      resize _ _ r3_value
  end.

Definition select_ctx type (reg_ctx frame_ctx: u128) :=
  match type with
  | Normal | Mimic => reg_ctx
  | Delegate => frame_ctx
  end.


(* Not implemented: shards *)
Inductive farcall (type:farcall_type) dest_addr handler_addr call_as_static abi_ptr_tag: FarCall.params -> state -> state -> Prop :=
| farcall_invoke: forall flags old_regs old_pages xstack0 xstack1 xstack2 new_caller_stack depot codes reg_context_u128 new_pages new_code_page mem_ctx1 new_mem_ctx in_ptr __ ergs_query ergs_actual fwd_mode is_syscall_query out_ptr,
    let old_extframe := topmost_extframe xstack0 in
    let mem_ctx0 := old_extframe.(ecf_pages) in
    let current_contract := old_extframe.(ecf_this_address) in
    let is_system := addr_is_kernel dest_addr && is_syscall_query in
    let allow_masking := negb is_system in

    (fwd_mode = ForwardFatPointer -> abi_ptr_tag = true) ->

    paid_code_fetch allow_masking depot codes dest_addr xstack0 (xstack1, new_code_page) ->
    paid_forward fwd_mode (in_ptr, xstack1, mem_ctx0) (out_ptr, xstack2, mem_ctx1)->
    alloc_pages_extframe (old_pages,mem_ctx1) new_code_page (new_pages, new_mem_ctx) ->
    pass_allowed_ergs (ergs_query,xstack2) (ergs_actual, new_caller_stack) ->

    let new_stack := ExternalCall {|
                         ecf_this_address := select_this_address type current_contract dest_addr;
                         ecf_msg_sender := select_sender type old_extframe.(ecf_msg_sender) current_contract old_regs;
                         ecf_context_u128_value := select_ctx type reg_context_u128 old_extframe.(ecf_context_u128_value);

                         ecf_code_address := zero16;
                         ecf_pages := new_mem_ctx;
                         ecf_is_static :=  ecf_is_static old_extframe || call_as_static;
                         ecf_saved_storage_state := load _ current_contract depot;
                         ecf_common := {|
                                        cf_exception_handler_location := handler_addr;
                                        cf_sp := INITIAL_SP_ON_FAR_CALL;
                                        cf_pc := zero16;
                                        cf_ergs_remaining := ergs_actual;
                                      |};
                       |} (Some new_caller_stack) in

    farcall type dest_addr handler_addr call_as_static abi_ptr_tag
            {|
              fc_memory_quasi_fat_ptr := in_ptr;
              fc_ergs_passed          := ergs_query;
              fc_shard_id             := __;
              fc_forwarding_mode      := fwd_mode;
              fc_constructor_call     := false;
              fc_to_system            := is_syscall_query;
            |}
            {|
              gs_flags        := flags;
              gs_regs         := old_regs;
              gs_pages        := old_pages;
              gs_callstack    := xstack0;
              gs_context_u128 := reg_context_u128;


              gs_depot        := depot;
              gs_contracts    := codes;
            |}
            {|
              gs_flags        := flags_clear;
              gs_regs         := regs_effect old_regs is_system false out_ptr;
              gs_pages        := new_pages;
              gs_callstack    := new_stack;
              gs_context_u128 := zero128;


              gs_depot        := depot;
              gs_contracts    := codes;
            |}
.

Inductive fetch_operands abi dest handler:
(contract_address * ExecutionStack.exception_handler * bool *  FarCall.params) -> Prop:=

| farcall_fetch: forall handler_location dest_val abi_val (abi_ptr_tag:bool) abi_params gs abi_ptr_tag,
    let fetch := resolve_fetch_value gs.(gs_regs) gs.(gs_callstack) gs.(gs_pages) in

    fetch dest dest_val ->
    fetch abi (mk_pv abi_ptr_tag abi_val) ->
    fetch handler (IntValue handler_location) ->

    FarCall.ABI.(decode) abi_val = Some abi_params ->

    let dest_addr := resize _ 160 dest_val.(value) in
    let handler_addr := resize _ code_address_bits handler_location in
    fetch_operands abi dest handler (dest_addr, handler_addr, abi_ptr_tag, abi_params).



(**
<<
# Possible exceptions
>>
 *)
Record FarCallExceptions : Set := {
    fce_input_is_not_pointer_when_expected : bool;
    fce_invalid_code_hash_format : bool;
    fce_not_enough_ergs_to_decommit : bool;
    fce_not_enough_ergs_to_grow_memory : bool;
    fce_malformed_abi_quasi_pointer : bool;
    fce_call_in_now_constructed_system_contract : bool;
    fce_note_enough_ergs_for_extra_far_call_costs : bool;
  }.
