From RecordUpdate Require Import RecordSet.
Require Common Ergs Condition CallStack Memory Instruction State MemoryOps ABI SemanticCommon.

Import
  BinIntDef.Z
    Bool
    List
    ListNotations
    ZArith
    ZMod.


Import
  Addressing
    ABI ABI.FarCall ABI.FatPointer
    CodeStorage
    Common
    Condition
    CodeStorage
    Ergs
    CallStack
    Memory
    MemoryBase
    MemoryOps
    Pages
    RecordSetNotations
    SemanticCommon
    State.

Import Instruction Addressing.Coercions.

Local Coercion Z.b2z: bool >-> Z.
Local Coercion int_mod_of : Z >-> int_mod.


(** # Far calls

Far calls are calls to the code outside the current contract space.
This file describes three instructions to perform far calls:

- [OpFarCall]
- [OpDelegateCall]
- [OpMimicCall] (available only in kernel mode)

These instructions differ in the way they construct new frame.

The far call instructions have rich semantics; their full effect on the
VM state is described through the following main predicates:

- [Semantics.step]
- [step]
- [fetch_operands]
- [farcall]

If you know about fetching operands for instructions and the instruction fetching described in [Semantics.step], start investigating farcalls from the [farcall] predicate.
 *)
Section Parameters.
  Open Scope Z.

  (**

## Global farcall parameters

1. Initial preallocated stack space.

   A far call creates a new context with a new stack page (and other pages, see
   [page_alloc]).
   The initial SP value after a far call is set to [INITIAL_SP_ON_FAR_CALL].

   Therefore, addresses in range from 0 inclusive to [INITIAL_SP_ON_FAR_CALL]
   exclusive can be used as a scratch space.
   *)

  Definition INITIAL_SP_ON_FAR_CALL : stack_address := 1024.

  (**
2. Initial heap and auxheap pages bound.

   The heap and auxheap pages start with [NEW_FRAME_MEMORY_STIPEND] bound.
   Growing them beyond this bound costs ergs.
   *)
  Definition NEW_FRAME_MEMORY_STIPEND : mem_address := 1024.

End Parameters.

(**
3. Maximal fraction of ergs allowed to pass.

   It is not allowed to pass more than 63/64th of your remaining ergs to a far call.
 *)
Definition max_passable (remaining:ergs) : ergs := (((int_val _ remaining) / 64 ) * 63)%Z.
Inductive pass_allowed_ergs : (ergs * callstack )-> ergs * callstack -> Prop :=
| pae_apply: forall xstack1 xstack2 pass_ergs_query,
    let pass_ergs_actual := ZMod.min _ (max_passable (ergs_remaining xstack1)) pass_ergs_query in
    pay pass_ergs_actual xstack1 xstack2 ->
    pass_ergs_query <> zero32 ->
    pass_allowed_ergs (pass_ergs_query,xstack1) (pass_ergs_actual, xstack2)
| pae_zero: forall xstack1 xstack2,
    let pass_ergs_actual := max_passable (ergs_remaining xstack1) in
    pay pass_ergs_actual xstack1 xstack2 ->
    pass_allowed_ergs (zero32, xstack1) (pass_ergs_actual, xstack2).


(**

## Helpers

Far call creates a new execution context with new pages for:

- code
- const (in the current implementation, const and code pages are the same page).
- stack
- heap
- auxheap

The initial bounds for the new heap and auxheap pages are set to [NEW_FRAME_MEMORY_STIPEND].
 *)
Inductive alloc_pages_extframe:  (memory * active_pages) -> code_page -> memory * active_pages -> Prop :=
| ape_alloc: forall code mm ctx code_id const_id stack_id heap_id heap_aux_id,
    code_id = length mm ->
    (const_id = code_id + 1)%nat ->
    (stack_id = code_id + 2)%nat ->
    (heap_id = code_id + 3)%nat ->
    (heap_aux_id = code_id + 4)%nat ->
    alloc_pages_extframe (mm,ctx) code
      ( (heap_aux_id, (DataPage _ (empty _)))::
          (heap_id, (DataPage _ (empty _)))::
          (stack_id, (StackPage _ (empty _)))::
          (const_id,(ConstPage _ (empty _)))::
          (code_id,(CodePage _ code))::mm,
        {|
          ctx_code_page_id := code_id;
          ctx_const_page_id := const_id;
          ctx_stack_page_id := stack_id;
          ctx_heap_page_id := heap_id;
          ctx_auxheap_page_id := heap_aux_id;
          ctx_heap_bound := NEW_FRAME_MEMORY_STIPEND;
          ctx_auxheap_bound := NEW_FRAME_MEMORY_STIPEND;
        |} ).

(**
Far call to a contract decommits the contract's code to a fresh code page.
If the code was already decommitted in the current block, this operation is free.
Otherwise, it costs the amount of ergs proportionate to the code size (in words).
 *)
Inductive decommitment_cost (cm:code_manager) vhash (code_length_in_words: code_length): ergs -> Prop :=
|dc_fresh: forall cost,
    is_fresh _ cm vhash = true->
    (cost, false) = Ergs.ERGS_PER_CODE_WORD_DECOMMITTMENT * (resize _ _ code_length_in_words) ->
    decommitment_cost cm vhash code_length_in_words cost
|dc_not_fresh:
  is_fresh _  cm vhash = false ->
  decommitment_cost cm vhash code_length_in_words zero32.

(** Fetch code and pay the associated cost. If [masking_allowed] is true and there is no code
associated with a given contract address, then the default AA code will be
fetched. See [code_fetch]. *)
Inductive paid_code_fetch masking_allowed sid: depot -> code_manager -> contract_address
                                           -> callstack -> callstack * code_page
                                           ->Prop :=
| cfp_apply:
  forall depot (codes:code_manager) (dest_addr: contract_address) vhash dest_addr new_code_page code_length cost__decomm xstack0 xstack1,

    code_fetch _ depot codes.(cm_storage _) sid dest_addr masking_allowed (vhash, new_code_page, code_length) ->
    decommitment_cost codes vhash code_length cost__decomm ->
    pay cost__decomm xstack0 xstack1 ->
    paid_code_fetch masking_allowed sid depot codes dest_addr xstack0 (xstack1, new_code_page).

(** ## System calls

A system call is a far call that satisfies the following conditions:

- The destination is a kernel address.
- The field `is_system` of [FarCall.params] passed through an operand is set to 1.
 *)


(** # Far call instructions

## Summary
 
- Far calls are calls to the code outside the current contract space.

- Mimic calls are a kernel-only variation of far calls allowing to mimic a call
  from any contract by impersonating an arbitrary caller and putting an arbitrary
  address into the new callframe's [ecf_msg_sender] field.

- Delegate calls are a variation of far calls allowing to call a contract with the current storage space.

  **Example**: Suppose we have contracts A,B,C. Contract A called contract B
    normally, then contract B delegated to contract C. Then C's code will be
    executed in a context of B's storage, as if contract A called contract C.
    If contract C returns normally, the execution will proceed from the next
    instruction of B after delegate call.
    In case of `revert` or `panic` in C, all the usual rules apply.

## Syntax

- [OpFarCall] `abi_params address handler is_static`
   + `farcall        abi_reg, dest_addr` 
   + `farcall        abi_reg, dest_addr, handler ` 
   + `farcall.static abi_reg, dest_addr` 
   + `farcall.static abi_reg, dest_addr, handler` 
   + `farcall.shard  abi_reg, dest_addr` 
   + `farcall.shard  abi_reg, dest_addr, handler` 

- [OpDelegateCall] abi_params address handler is_static`
   + `delegatecall        abi_reg, dest_addr` 
   + `delegatecall        abi_reg, dest_addr, handler` 
   + `delegatecall.static abi_reg, dest_addr` 
   + `delegatecall.static abi_reg, dest_addr, handler` 
   + `delegatecall.shard  abi_reg, dest_addr` 
   + `delegatecall.shard  abi_reg, dest_addr, handler` 

- [OpMimicCall] `abi_params address handler is_static`
   + `mimic        abi_reg, dest_addr` 
   + `mimic        abi_reg, dest_addr, handler` 
   + `mimic.static abi_reg, dest_addr` 
   + `mimic.static abi_reg, dest_addr, handler` 
   + `mimic.shard  abi_reg, dest_addr` 
   + `mimic.shard  abi_reg, dest_addr, handler` 


- **static** modifier marks the new execution stack frame as 'static', preventing some instructions from being executed.
  Calls from a static calls are automatically marked static.

- **shard** modifier allows calling code from other shards. The shard ID will be taken from `abi_reg`.

## Semantic

The semantics of all three 
First two steps are formalized by predicates [Semantics.step] and [fetch_operands].

1. Fetch the instruction, adjust PC and perform the usual checks (such as kernel
   mode), pay basic costs, and so on.

   See [Semantics.step] for details.

2. Retrieve the operands and decode the following structure from `abi_reg`:
   
```
   Record params := {
       memory_quasi_fat_ptr: fat_ptr;
       ergs_passed: ergs;
       shard_id: u8;
       forwarding_mode: forward_page_type;
       constructor_call: bool;
       to_system: bool;
     }.
```

   See [fetch_operands] for details.
   
   The [farcall] predicate encodes the important part of instruction semantics for
   [OpFarCall], [OpDelegateCall], and [OpMimicCall].

3. Decommit code of the callee contract (formalized by [paid_code_fetch]):

   - load the [versioned_hash] of the called code from the storage of a
     special contract located at [DEPLOYER_SYSTEM_CONTRACT_ADDRESS].

```
Inductive marker := CODE_AT_REST | YET_CONSTRUCTED | INVALID.

Record versioned_hash := {
   code_length_in_words: u16;
   extra_marker: marker;
   partial_hash: int_mod (28*8)%nat
}.
```
   - for non-system calls, if there is no code stored for a provided hash value,
     mask it into [VersionedHash.DEFAULT_AA_VHASH] and execute
     [VersionedHash.DEFAULT_AA_CODE].

   - if the code with such hash has not been accessed in the current block, pay
     for decommitment.

4. Forward data to the new frame (formalized by [paid_forward_and_adjust_bounds]).

   - use the forwarding mode from `abi_reg` -> [forwarding_mode]. Can be `ForwardFatPointer`, `UseHeap` or `UseAuxHeap`;
   - take the fat pointer to the data slice is taken from `abi_reg` -> [memory_quasi_fat_ptr];
   - for the forwarding mode `ForwardFatPointer`:
     - check the pointer validity;
     - shrink the pointer;
     - ensure that `abi_reg` is tagged as a pointer.
   - for the forwarding modes `UseHeap`/`UseAuxHeap`:
     - check the pointer validity;
     - overwrite the pointer's [page_id] with the ID of current (aux)heap's memory page;
     - if the pointer bounds surpass current heap/auxheap bounds, pay for growth
       and adjust the bounds of heap/auxheap in the current stack frame.

5. Allocate new pages for code, constants, stack, heap and auxheap (formalized by [alloc_pages_extframe]).
6. Reserve ergs for the new external frame (formalized by [pass_allowed_ergs]).

   - Maximum amount of ergs passed to an external call is 63/64 of current balance.
   - Attempting to pass more ergs will result in only passing the maximum amount allowed.
   - Trying to pass 0 ergs will result in passing maximum amount of ergs allowed.

7. Clear the context register.
8. Clear flags.
9. Modify GPRs depending on the call being system or not (formalized by [regs_effect]):

  - Effect of a non-system call:
    + All registers are cleared.
    + Register `R1` is assigned a fat pointer to forward data to the far call.
      See [paid_forward].

  - Effect of a system call:
    + Register `R1` is assigned a fat pointer to forward data to the far call.
      See [paid_forward].
    + Register `R2` is assigned a bit-value:
      - bit 1 indicates "this is a system call"
      - bit 0 indicates "this is a constructor call"
    + Registers `r3`, `r4`, ..., `r15` are reserved; their pointer tags are
      cleared, but their values are unchanged.
    + Registers `r14` and `r15` are cleared.
 *)
Definition regs_effect regs (is_system is_ctor:bool) ptr :=
  let far_call_r2 :=
    let is_system_bit := Z.shiftl is_system 1 in
    let is_ctor_bit := Z.shiftl is_ctor 0 in
    let bits := Z.lor is_system_bit is_ctor_bit in
    IntValue (int_mod_of word_bits bits) in
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
(*
10. Form a new execution stack frame:

   - the call is static if the current call is static, or if `.is_static` modifier is applied to instruction;
   - set exception handler to `handler` address provided in the instruction;
   - it is a checkpoint that saves all storage states;
   - start PC at 0;
   - start SP at [INITIAL_SP_ON_FAR_CALL];
 *)

Definition CALL_IMPLICIT_PARAMETER_REG := R3.
Inductive farcall_type : Set := Normal | Mimic | Delegate.

(**

   - `this_address`,`msg_sender` and `context` fields are affected by the [farcall_type] as follows:
      + Normal far call sets:
        * `this_address` <- destination address;
        * `msg_sender` <- caller address;
        * `context` <- value of context register [gs_context_u128].
      
      + Delegate call sets:
        * `this_address` <- [this_address] of the current frame;
        * `msg_sender` <- [msg_sender] of the current frame;
        * `context` <- [context_u128] of the current frame.
      
      + Mimic call sets:
        * `this_address` <- destination address;
        * `msg_sender` <- value of `r3`;
        * `context` <- value of context register [gs_context_u128].
      
 *)
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

Definition new_code_shard_id (is_call_shard:bool)
  (provided current_shard:shard_id) : shard_id :=
  if is_call_shard then provided else current_shard.

Definition select_shards (type: farcall_type) (is_call_shard: bool) (provided: shard_id) (ss: active_shards) : active_shards :=
  match ss with
  | mk_shards old_this _ code =>
      let new_caller := old_this in
      let new_code := new_code_shard_id is_call_shard provided new_caller in
      let new_this := match type with | Delegate => new_caller | _ => new_code end in
      {|
        shard_this := new_this;
        shard_caller := new_caller;
        shard_code := new_code;
      |}       
  end. 

Section Def.

  Context (type:farcall_type) (dest_addr:contract_address) (handler_addr: code_address)
    (call_as_static: bool) (to_abi_shard: bool) (abi_ptr_tag: bool).

  Context (xstack0: callstack).
  
  Let old_extframe := topmost_extframe xstack0.
  Let mem_ctx0 := old_extframe.(ecf_memory).
  Let current_contract := old_extframe.(ecf_this_address).
  
  (* Not implemented yet: shards *)
  Inductive farcall : FarCall.params -> state -> state -> Prop :=
  | farcall_fwd_fatptr: forall flags old_regs old_pages xstack0 xstack1 xstack2 new_caller_stack gs reg_context_u128 new_pages new_code_page new_mem_ctx in_ptr abi_shard ergs_query ergs_actual fwd_mode is_syscall_query out_ptr,
      let is_system := addr_is_kernel dest_addr && is_syscall_query in
      let allow_masking := negb is_system in
      let callee_shard := if to_abi_shard then abi_shard else old_extframe.(ecf_shards).(shard_this) in
      abi_ptr_tag = true ->
      
      paid_code_fetch allow_masking callee_shard gs.(gs_revertable).(gs_depot) gs.(gs_contracts) dest_addr xstack0 (xstack1, new_code_page) ->
      paid_forward Ret.ForwardFatPointer (in_ptr, xstack1) (out_ptr, xstack2) ->
      alloc_pages_extframe (old_pages,mem_ctx0) new_code_page (new_pages, new_mem_ctx) ->
      pass_allowed_ergs (ergs_query,xstack2) (ergs_actual, new_caller_stack) ->

      let new_stack := ExternalCall {|
                           ecf_this_address := select_this_address type current_contract dest_addr;
                           ecf_msg_sender := select_sender type old_extframe.(ecf_msg_sender) current_contract old_regs;
                           ecf_context_u128_value := select_ctx type reg_context_u128 old_extframe.(ecf_context_u128_value);

                           ecf_code_address := dest_addr;
                           ecf_memory := new_mem_ctx;
                           ecf_is_static :=  ecf_is_static old_extframe || call_as_static;
                           ecf_saved_checkpoint := gs.(gs_revertable);
                           ecf_shards := select_shards type to_abi_shard abi_shard old_extframe.(ecf_shards);
                           ecf_common := {|
                                          cf_exception_handler_location := handler_addr;
                                          cf_sp := INITIAL_SP_ON_FAR_CALL;
                                          cf_pc := zero16;
                                          cf_ergs_remaining := ergs_actual;
                                        |};
                         |} (Some new_caller_stack) in

      farcall
        {|
          memory_quasi_fat_ptr := in_ptr;
          ergs_passed          := ergs_query;
          FarCall.shard_id     := abi_shard;
          forwarding_mode      := fwd_mode;
          constructor_call     := false;
          to_system            := is_syscall_query;
        |}
        {|
          gs_xstate := {|
                        gs_flags        := flags;
                        gs_regs         := old_regs;
                        gs_pages        := old_pages;
                        gs_callstack    := xstack0;
                      |};
          gs_context_u128 := reg_context_u128;

          gs_global       := gs;
        |}
        {|
          gs_xstate := {|
                        gs_flags        := flags_clear;
                        gs_regs         := regs_effect old_regs is_system false out_ptr;
                        gs_pages        := new_pages;
                        gs_callstack    := new_stack;
                      |};
          gs_context_u128 := zero128;


          gs_global       := gs;
        |}
  | farcall_fwd_memory: forall gs flags old_regs old_pages xstack0 xstack1 xstack2 new_caller_stack reg_context_u128 new_pages new_code_page new_mem_ctx in_ptr abi_shard ergs_query ergs_actual is_syscall_query out_ptr page_type,
      let is_system := addr_is_kernel dest_addr && is_syscall_query in
      let allow_masking := negb is_system in
      let callee_shard := if to_abi_shard then abi_shard else old_extframe.(ecf_shards).(shard_this) in

      paid_code_fetch allow_masking callee_shard gs.(gs_revertable).(gs_depot) gs.(gs_contracts) dest_addr xstack0 (xstack1, new_code_page) ->
      paid_forward (Ret.UseMemory page_type) (in_ptr, xstack1) (out_ptr, xstack2) ->
      
      let mem_ctx1 := (topmost_extframe xstack2).(ecf_memory) in
      alloc_pages_extframe (old_pages, mem_ctx1) new_code_page (new_pages, new_mem_ctx) ->
      pass_allowed_ergs (ergs_query,xstack2) (ergs_actual, new_caller_stack) ->

      let new_stack := ExternalCall {|
                           ecf_this_address := select_this_address type current_contract dest_addr;
                           ecf_msg_sender := select_sender type old_extframe.(ecf_msg_sender) current_contract old_regs;
                           ecf_context_u128_value := select_ctx type reg_context_u128 old_extframe.(ecf_context_u128_value);

                           ecf_shards := select_shards type to_abi_shard abi_shard old_extframe.(ecf_shards);
                           ecf_code_address := dest_addr;
                           ecf_memory:= new_mem_ctx;
                           ecf_is_static :=  ecf_is_static old_extframe || call_as_static;
                           ecf_saved_checkpoint := gs.(gs_revertable);
                           ecf_common := {|
                                          cf_exception_handler_location := handler_addr;
                                          cf_sp := INITIAL_SP_ON_FAR_CALL;
                                          cf_pc := zero16;
                                          cf_ergs_remaining := ergs_actual;
                                        |};
                         |} (Some new_caller_stack) in

      farcall 
        {|
          memory_quasi_fat_ptr := in_ptr;
          ergs_passed          := ergs_query;
          FarCall.shard_id     := abi_shard;
          forwarding_mode      := Ret.UseMemory page_type;
          constructor_call     := false;
          to_system            := is_syscall_query;
        |}
        {|
          gs_xstate := {|
                        gs_flags        := flags;
                        gs_regs         := old_regs;
                        gs_pages        := old_pages;
                        gs_callstack    := xstack0;
                      |};
          gs_context_u128 := reg_context_u128;


          gs_global       := gs;
        |}
        {|
          gs_xstate := {|
                        gs_flags        := flags_clear;
                        gs_regs         := regs_effect old_regs is_system false out_ptr;
                        gs_pages        := new_pages;
                        gs_callstack    := new_stack;
                      |};
          gs_context_u128 := zero128;

          gs_global       := gs;
        |}
  .
End Def.

Inductive fetch_operands abi dest handler:
  (contract_address * exception_handler * bool *  FarCall.params) -> Prop:=

| farcall_fetch: forall handler_location dest_val abi_val (abi_ptr_tag:bool) abi_params gs abi_ptr_tag,
    let resolve_loads := resolve_loads gs.(gs_callstack) (gs.(gs_regs),gs.(gs_pages)) in

    resolve_loads [
        (dest,dest_val);
        (abi, mk_pv abi_ptr_tag abi_val);
        (handler, IntValue handler_location)]
    ->

    FarCall.ABI.(decode) abi_val = Some abi_params ->

    let dest_addr := resize _ 160 dest_val.(value) in
    let handler_addr := resize _ code_address_bits handler_location in
    fetch_operands abi dest handler (dest_addr, handler_addr, abi_ptr_tag, abi_params).

Inductive step : instruction -> smallstep :=
  
| step_farcall_normal: forall (handler:imm_in) (abi dest:in_reg) call_shard call_as_static dest_addr handler_addr abi_ptr_tag abi_params (gs gs':state),

    fetch_operands abi dest handler (dest_addr, handler_addr, abi_ptr_tag, abi_params)->
    farcall Normal dest_addr handler_addr call_as_static abi_ptr_tag call_shard gs.(gs_callstack) abi_params gs gs' ->

    step (OpFarCall abi dest handler call_shard call_as_static) gs gs'

| step_mimic: forall (handler:imm_in) (abi dest:in_reg) call_as_static dest_addr handler_addr abi_ptr_tag abi_params (gs gs':state) call_shard,

    fetch_operands abi dest handler (dest_addr, handler_addr, abi_ptr_tag, abi_params)->
    farcall Mimic dest_addr handler_addr call_as_static abi_ptr_tag call_shard gs.(gs_callstack) abi_params gs gs' ->

    step (OpMimicCall abi dest handler call_shard call_as_static) gs gs'
| step_delegate: forall (handler:imm_in) (abi dest:in_reg) call_as_static dest_addr handler_addr abi_ptr_tag abi_params (gs gs':state) call_shard,

    fetch_operands abi dest handler (dest_addr, handler_addr, abi_ptr_tag, abi_params)->
    farcall Delegate dest_addr handler_addr call_as_static abi_ptr_tag call_shard gs.(gs_callstack) abi_params gs gs' ->

    step (OpDelegateCall abi dest handler call_shard  call_as_static) gs gs'
.

(**

## Affected parts of VM state

- flags are cleared
- registers are affected as described by [regs_effect].
- new pages appear as described by [alloc_pages_extframe].
- context register is zeroed.
- execution stack is affected in a non-trivial way (see step 10 in description for [farcall]).

## Comparison with near calls

- Far calls can not accept more than [max_passable] ergs, while near calls may accept all available ergs.
- Abnormal returns from far calls through [OpPanic] or [OpRevert] roll back all
storage changes that occured during the contract execution.

This includes exceptional situations when an error occured and the current
instruction is masked as [OpPanic].


## Usage

- Calling precompiles
- Calling other contracts

## Encoding

- In the encoding, [OpDelegateCall], [OpFarCall], and [OpMimicCall] share the same opcode.


# Possible exceptions

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
