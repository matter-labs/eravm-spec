From RecordUpdate Require Import RecordSet.

Require Common Decommitter Ergs CallStack Memory isa.CoreSet State MemoryOps MemoryManagement ABI Pointer SemanticCommon.

Import
  BinIntDef.Z
    Bool
    List
    ListNotations
    ZArith.

Import
  Addressing
    ABI ABI.FarCall ABI.FatPointer
    Decommitter
    Common
    Core
    isa.CoreSet
    Coder
    Flags
    GPR
    Ergs
    CallStack
    KernelMode
    Memory
    MemoryBase
    MemoryOps
    MemoryContext
    MemoryManagement
    PrimitiveValue
    RecordSetNotations
    VersionedHash
    SemanticCommon
    State.

Import Addressing.Coercions.

Local Coercion Z.b2z: bool >-> Z.

(** # Far calls

Far calls are calls to the code outside the current contract space.
This section describes three instructions to perform far calls:

- [%OpFarCall]
- [%OpDelegateCall]
- [%OpMimicCall] (available only in kernel mode)

These instructions differ in the way they construct new frame.

The far call instructions have rich semantics; their full effect on the
VM state is described through the following main predicates:

- [%Semantics.step]
- [%step]
- [%fetch_operands]
- [%farcall]

If you know about fetching operands for instructions and the instruction fetching described in [%Semantics.step], start investigating farcalls from the [%farcall] predicate.
 *)
Section Parameters.
  Open Scope Z_scope.
  Open Scope ZMod_scope.

  (**

## Global farcall parameters

1. Initial preallocated stack space.

   A far call creates a new context with a new stack page (and other pages, see
   [%page_alloc]).
   The initial SP value after a far call is set to [%INITIAL_SP_ON_FAR_CALL].

   Therefore, addresses in range from 0 inclusive to [%INITIAL_SP_ON_FAR_CALL]
   exclusive can be used as a scratch space.
   *)

  Definition INITIAL_SP_ON_FAR_CALL : stack_address := fromZ 1024.

  (**
2. Initial heap and auxheap pages bound.

   The heap and auxheap pages start with [%NEW_FRAME_MEMORY_STIPEND] bound.
   Growing them beyond this bound costs ergs.
   *)
  Definition NEW_FRAME_MEMORY_STIPEND : mem_address := fromZ 1024.

End Parameters.

(**
3. Maximal fraction of ergs allowed to pass.

   It is not allowed to pass more than 63/64th of your remaining ergs to a far call.
 *)
Definition max_passable (remaining:ergs) : ergs := fromZ (toZ remaining * 63 / 64 ) %Z.
Inductive pass_allowed_ergs : (ergs * callstack )-> ergs * callstack -> Prop :=
| pae_apply: forall cs1 cs2 pass_ergs_query,
    let pass_ergs_actual := min (max_passable (ergs_remaining cs1)) pass_ergs_query in
    pay pass_ergs_actual cs1 cs2 ->
    pass_ergs_query <> zero32 ->
    pass_allowed_ergs (pass_ergs_query,cs1) (pass_ergs_actual, cs2)
| pae_zero: forall cs1 cs2,
    let pass_ergs_actual := max_passable (ergs_remaining cs1) in
    pay pass_ergs_actual cs1 cs2 ->
    pass_allowed_ergs (zero32, cs1) (pass_ergs_actual, cs2).


(**

## Helpers

Far call creates a new execution context with new pages for:

- code
- const (in the current implementation, const and code pages are the same page).
- stack
- heap
- auxheap

The initial bounds for the new heap and auxheap pages are set to [%NEW_FRAME_MEMORY_STIPEND].
 *)
Inductive alloc_pages_extframe:  pages * mem_ctx -> code_page -> const_page -> pages * mem_ctx -> Prop :=
| ape_alloc: forall code const (mm:pages) ctx code_id const_id stack_id heap_id heap_aux_id,
    code_id = length mm ->
    (const_id = code_id + 1)%nat ->
    (stack_id = code_id + 2)%nat ->
    (heap_id = code_id + 3)%nat ->
    (heap_aux_id = code_id + 4)%nat ->
    alloc_pages_extframe (mm,ctx) code const
      ( (heap_aux_id, (mk_page (DataPage (empty data_page_params))))::
          (heap_id, (mk_page (DataPage (empty _))))::
          (stack_id, (mk_page (StackPage (empty stack_page_params))))::
          (const_id,(mk_page (ConstPage const)))::
          (code_id, (mk_page (CodePage code)))::mm,
        {|
          ctx_code_page_id := code_id;
          ctx_const_page_id := const_id;
          ctx_stack_page_id := stack_id;
          ctx_heap_page_id := heap_id;
          ctx_auxheap_page_id := heap_aux_id;
          ctx_heap_bound := NEW_FRAME_MEMORY_STIPEND;
          ctx_auxheap_bound := NEW_FRAME_MEMORY_STIPEND;
        |} ).

Inductive alloc_mem_extframe: memory * mem_ctx -> code_page -> const_page -> memory * mem_ctx -> Prop :=
| ame_apply: forall p c p' c' code const,
    alloc_pages_extframe (p,c) code const (p',c') ->
    alloc_mem_extframe (mk_pages p,c) code const (mk_pages p',c').

(** Fetch code and pay the associated cost. If [%masking_allowed] is true and there is no code
associated with a given contract address, then the default AA code will be
fetched. See [%code_fetch]. *)
Inductive paid_code_fetch_result :=
| Fetched : callstack -> code_page -> const_page -> paid_code_fetch_result
| CodeFetchInvalidVerisonedHashFormat (_:versioned_hash)
| CodeFetchUnaffordable (cost:ergs)
.

Inductive paid_code_fetch masking_allowed sid: depot -> decommitter -> contract_address -> callstack -> paid_code_fetch_result ->Prop :=
| cfp_fetched:
  forall depot (codes:decommitter) (dest_addr: contract_address) vhash dest_addr new_code_page new_const_page code_length cost__decomm cs0 cs1,

    code_fetch _ depot codes.(cm_storage _) sid dest_addr masking_allowed (vhash, (new_code_page, new_const_page), code_length) ->
    decommitment_cost _ codes vhash code_length cost__decomm ->
    pay cost__decomm cs0 cs1 ->
    paid_code_fetch masking_allowed sid depot codes dest_addr cs0 (Fetched cs1 new_code_page new_const_page)
| cfp_unaffordable:
  forall depot (codes:decommitter) (dest_addr: contract_address) vhash dest_addr new_code_page new_const_page code_length cost__decomm cs0 ,
    code_fetch _ depot codes.(cm_storage _) sid dest_addr masking_allowed (vhash, (new_code_page, new_const_page), code_length) ->
    decommitment_cost _ codes vhash code_length cost__decomm ->
    affordable cs0 cost__decomm = false ->
    paid_code_fetch masking_allowed sid depot codes dest_addr cs0 (CodeFetchUnaffordable cost__decomm)

| cfp_invalid_hash:
  forall depot (codes:decommitter) (dest_addr: contract_address) vhash dest_addr new_code_page new_const_page code_length cs0 ,
    code_fetch _ depot codes.(cm_storage _) sid dest_addr masking_allowed (vhash, (new_code_page, new_const_page), code_length) ->
    marker_valid (extra_marker vhash) = false ->
    paid_code_fetch masking_allowed sid depot codes dest_addr cs0 (CodeFetchInvalidVerisonedHashFormat vhash)
.

(** ## System calls

A system call is a far call that satisfies the following conditions:

- The destination is a kernel address.
- The field `is_system` of [%FarCall.params] passed through an operand is set to 1.
 *)


(** # Far call instructions

## Summary

- Far calls are calls to the code outside the current contract space.

- Mimic calls are a kernel-only variation of far calls allowing to mimic a call
  from any contract by impersonating an arbitrary caller and putting an arbitrary
  address into the new callframe's [%ecf_msg_sender] field.

- Delegate calls are a variation of far calls allowing to call a contract with the current storage space.

  **Example**: Suppose we have contracts A,B,C. Contract A called contract B
    normally, then contract B delegated to contract C. Then C's code will be
    executed in a context of B's storage, as if contract A called contract C.
    If contract C returns normally, the execution will proceed from the next
    instruction of B after delegate call.
    In case of `revert` or `panic` in C, all the usual rules apply.

## Abstract and concrete syntax

- [%OpFarCall] `abi_params address handler is_static swap `
   + `farcall        abi_reg, dest_addr`
   + `farcall        abi_reg, dest_addr, handler `
   + `farcall.static abi_reg, dest_addr`
   + `farcall.static abi_reg, dest_addr, handler`
   + `farcall.shard  abi_reg, dest_addr`
   + `farcall.shard  abi_reg, dest_addr, handler`

   These variants also support the `.s` swap modifier.

- [%OpDelegateCall] abi_params address handler is_static swap `
   + `delegatecall        abi_reg, dest_addr`
   + `delegatecall        abi_reg, dest_addr, handler`
   + `delegatecall.static abi_reg, dest_addr`
   + `delegatecall.static abi_reg, dest_addr, handler`
   + `delegatecall.shard  abi_reg, dest_addr`
   + `delegatecall.shard  abi_reg, dest_addr, handler`

   These variants also support the `.s` swap modifier.

- [%OpMimicCall] `abi_params address handler is_static swap`
   + `mimic        abi_reg, dest_addr`
   + `mimic        abi_reg, dest_addr, handler`
   + `mimic.static abi_reg, dest_addr`
   + `mimic.static abi_reg, dest_addr, handler`
   + `mimic.shard  abi_reg, dest_addr`
   + `mimic.shard  abi_reg, dest_addr, handler`

   These variants also support the `.s` swap modifier.

- **static** modifier marks the new execution stack frame as 'static', preventing some instructions from being executed.
  Calls from a static calls are automatically marked static.

- **shard** modifier allows calling code from other shards. The shard ID will be taken from `abi_reg`.

## Semantic

1. Decode the structure `params` from `abi_reg`:

```
   Inductive fwd_memory :=
     ForwardFatPointer (p:fat_ptr)
   | ForwardNewFatPointer (heap_var: data_page_type) (s:span).


  Record params :=
    mk_params {
        fwd_memory: fwd_memory;
        ergs_passed: ergs;
        shard_id: shard_id;
        constructor_call: bool;
        to_system: bool;
      }.
```

3. Decommit code of the callee contract (formalized by [%paid_code_fetch]):

   - load the [%versioned_hash] of the called code from the storage of a
     special contract located at [%DEPLOYER_SYSTEM_CONTRACT_ADDRESS].

     ```
     Inductive marker := CODE_AT_REST | YET_CONSTRUCTED | INVALID.

     Record versioned_hash := {
        code_length_in_words: u16;
        extra_marker: marker;
        partial_hash: int_mod (28*8)%nat
     }.
     ```
   - for non-system calls, if there is no code stored for a provided hash value,
     mask it into [%VersionedHash.DEFAULT_AA_VHASH] and execute
     [%VersionedHash.DEFAULT_AA_CODE].

   - if the code with such hash has not been accessed in the current block, pay
     for decommitment.

4. Forward data to the new frame (formalized by [%paid_forward_and_adjust_bounds]).
   - If [%params.(fwd_memory)] is [%ForwardExistingFatPointer p], we are forwarding an existing fat pointer.
     - ensure that `abi_reg` is tagged as a pointer.
     - check the pointer validity;
     - [%fat_ptr_narrow] the pointer;
   - If [%params.(fwd_memory)] is [%ForwardNewFatPointer variant span], a new
     [%fat_ptr] is created. This pointer refers to the provided [%span] of
     specified heap `variant`.

5. Allocate new pages for code, constants, stack, heap and auxheap (formalized by [%alloc_pages_extframe]).
6. Reserve ergs for the new external frame (formalized by [%pass_allowed_ergs]).

   - Maximum amount of ergs passed to an external call is 63/64 of ergs allocated for the caller.
   - Attempting to pass more ergs will result in only passing the maximum amount allowed.
   - Trying to pass 0 ergs will result in passing maximum amount of ergs allowed.

7. Clear the context register.
8. Clear flags.
9. Modify GPRs depending on the call being system or not (formalized by [%regs_effect]):

  - Effect of a non-system call:
    + All registers are cleared.
    + Register `R1` is assigned a fat pointer to forward data to the far call.
      See [%paid_forward].

  - Effect of a system call:
    + Register `R1` is assigned a fat pointer to forward data to the far call.
      See [%paid_forward].
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
    IntValue (fromZ bits) in
  let enc_ptr := FatPointer.ABI.(encode) ptr in
  if is_system then
    regs
      <| r1 := PtrValue enc_ptr |>
      <| r2 := far_call_r2      |>
(* In system calls, preserve values in r3-r13 but clear ptr tags *)
      <| r3 ::= clear_pointer_tag |>
      <| r4 ::= clear_pointer_tag |>
      <| r5 ::= clear_pointer_tag |>
      <| r6 ::= clear_pointer_tag |>
      <| r7 ::= clear_pointer_tag |>
      <| r8 ::= clear_pointer_tag |>
      <| r9 ::= clear_pointer_tag |>
      <| r10 ::= clear_pointer_tag |>
      <| r11 ::= clear_pointer_tag |>
      <| r12 ::= clear_pointer_tag |>
      <| r13 ::= clear_pointer_tag |>
      (* zero the rest *)
      <| r14 := IntValue word0 |>
      <| r15 := IntValue word0 |>
  else
    regs_state_zero <| r1 := PtrValue enc_ptr |>.
(**
10. Form a new execution stack frame:

   - the call is static if the current call is static, or if `.is_static` modifier is applied to instruction;
   - set exception handler to `handler` address provided in the instruction;
   - it is a checkpoint that saves all storage states;
   - start PC at 0;
   - start SP at [%INITIAL_SP_ON_FAR_CALL];
 *)

Definition CALL_IMPLICIT_PARAMETER_REG := R15.
Inductive farcall_type : Set := Normal | Mimic | Delegate.

(**

   - `this_address`,`msg_sender` and `context` fields are affected by the [%farcall_type] as follows:
      + Normal far call sets:
        * `this_address` <- destination address;
        * `msg_sender` <- caller address;
        * `context` <- value of context register [%gs_context_u128].

      + Delegate call sets:
        * `this_address` <- [%this_address] of the current frame;
        * `msg_sender` <- [%msg_sender] of the current frame;
        * `context` <- [%context_u128] of the current frame.

      + Mimic call sets:
        * `this_address` <- destination address;
        * `msg_sender` <- value of `r3`;
        * `context` <- value of context register [%gs_context_u128].
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
      let r15_value := (fetch_gpr regs CALL_IMPLICIT_PARAMETER_REG).(value) in
      low contract_address_bits r15_value
  end.

Definition select_associated_contracts type regs (ac:associated_contracts) (call_dest: contract_address): associated_contracts :=
  match ac with
  | mk_assoc_contracts this_address msg_sender code_address =>
      {|
        ecf_this_address := select_this_address type this_address call_dest;
        ecf_msg_sender := select_sender type ac.(ecf_msg_sender) this_address regs;
        ecf_code_address := call_dest;
      |}
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

Section FarCallDefinitions.

  Import Pointer.
  Context (type:farcall_type) (is_static_call is_shard_provided:bool) (dest:contract_address) (handler: code_address) (gs:global_state).

  Inductive farcall : FarCall.params * @primitive_value word -> tsmallstep :=

  | farcall_fwd_existing_fatptr: forall flags old_regs old_pages cs0 cs1 new_caller_stack new_stack  reg_context_u128 new_pages new_code_page new_const_page new_mem_ctx (in_ptr narrowed_ptr: fat_ptr) abi_shard ergs_query ergs_actual is_syscall_query __,

      let caller_extframe := active_extframe cs0 in
      let mem_ctx0 := ecf_mem_ctx caller_extframe in
      let is_system := addr_is_kernel dest && is_syscall_query in
      let allow_masking := negb is_system in
      let callee_shard := if is_shard_provided then abi_shard else current_shard cs0 in

      paid_code_fetch allow_masking callee_shard (gs_depot gs) (gs_contracts gs) dest cs0 (Fetched cs1 new_code_page new_const_page) ->

      (*!*)validate in_ptr = no_exceptions ->
      (*!*)fat_ptr_narrow in_ptr narrowed_ptr ->

      alloc_pages_extframe (old_pages, mem_ctx0) new_code_page new_const_page (new_pages, new_mem_ctx) ->
      pass_allowed_ergs (ergs_query,cs1) (ergs_actual, new_caller_stack) ->

      new_stack = ExternalCall {|
                           ecf_associated         := select_associated_contracts type old_regs caller_extframe.(ecf_associated) dest;
                           ecf_context_u128_value := select_ctx type reg_context_u128 caller_extframe.(ecf_context_u128_value);
                           ecf_shards             := select_shards type is_shard_provided abi_shard caller_extframe.(ecf_shards);

                           ecf_mem_ctx := new_mem_ctx;
                           ecf_is_static :=  ecf_is_static caller_extframe || is_static_call;
                           ecf_common := {|
                                          cf_exception_handler_location := handler;
                                          cf_sp := INITIAL_SP_ON_FAR_CALL;
                                          cf_pc := zero16;
                                          cf_ergs_remaining := ergs_actual;
                                          cf_saved_checkpoint := gs.(gs_revertable);
                                        |};
                         |} (Some new_caller_stack) ->

      farcall
        ({|
          FarCall.fwd_memory           := ForwardExistingFatPointer in_ptr;
          ergs_passed          := ergs_query;
          FarCall.shard_id     := abi_shard;
          constructor_call     := false;
          to_system            := is_syscall_query;
        |},
        PtrValue __)
        {|
          gs_flags        := flags;
          gs_regs         := old_regs;
          gs_pages        := old_pages;
          gs_callstack    := cs0;
          gs_context_u128 := reg_context_u128;
          gs_status       := NoPanic;
        |}
        {|
          gs_flags        := flags_clear;
          gs_regs         := regs_effect old_regs is_system false narrowed_ptr;
          gs_pages        := new_pages;
          gs_callstack    := new_stack;
          gs_context_u128 := zero128;
          gs_status       := NoPanic;
        |}

  | farcall_fwd_new_ptr: forall flags old_regs old_pages cs0 cs1 cs2 new_caller_stack new_stack reg_context_u128 new_pages new_code_page new_const_page new_mem_ctx abi_shard ergs_query ergs_actual is_syscall_query out_ptr __ in_span page_type,

      let is_system := addr_is_kernel dest && is_syscall_query in
      let allow_masking := negb is_system in
      let callee_shard := if is_shard_provided then abi_shard else current_shard cs0 in

      paid_code_fetch allow_masking callee_shard
        gs.(gs_revertable).(gs_depot) gs.(gs_contracts) dest cs0 (Fetched cs1 new_code_page new_const_page) ->

      (*!*)paid_forward_new_fat_ptr page_type in_span cs0 (out_ptr, cs1) ->

      let caller_extframe := active_extframe cs2 in
      let mem_ctx0 := caller_extframe.(ecf_mem_ctx) in
      alloc_pages_extframe (old_pages, mem_ctx0) new_code_page new_const_page (new_pages, new_mem_ctx) ->
      pass_allowed_ergs (ergs_query,cs2) (ergs_actual, new_caller_stack) ->

      new_stack = ExternalCall {|
                           ecf_associated         := select_associated_contracts type old_regs caller_extframe.(ecf_associated) dest;
                           ecf_context_u128_value := select_ctx type reg_context_u128 caller_extframe.(ecf_context_u128_value);
                           ecf_shards             := select_shards type is_shard_provided abi_shard caller_extframe.(ecf_shards);

                           ecf_mem_ctx := new_mem_ctx;
                           ecf_is_static :=  ecf_is_static caller_extframe || is_static_call;
                           ecf_common := {|
                                          cf_exception_handler_location := handler;
                                          cf_sp := INITIAL_SP_ON_FAR_CALL;
                                          cf_pc := zero16;
                                          cf_ergs_remaining := ergs_actual;
                                          cf_saved_checkpoint := gs.(gs_revertable);
                                        |};
                         |} (Some new_caller_stack) ->

      farcall
        ({|
          FarCall.fwd_memory   := ForwardNewFatPointer page_type in_span;
          ergs_passed          := ergs_query;
          FarCall.shard_id     := abi_shard;
          constructor_call     := false;
          to_system            := is_syscall_query;
(*!*)   |}, __)
        {|
          gs_flags        := flags;
          gs_regs         := old_regs;
          gs_pages        := old_pages;
          gs_callstack    := cs0;
          gs_context_u128 := reg_context_u128;
          gs_status       := NoPanic;
        |}
        {|
          gs_flags        := flags_clear;
          gs_regs         := regs_effect old_regs is_system false out_ptr;
          gs_pages        := new_pages;
          gs_callstack    := new_stack;
          gs_context_u128 := zero128;
          gs_status       := NoPanic;
        |}
(**

## Affected parts of VM state

- flags are cleared
- registers are affected as described by [%regs_effect].
- new pages appear as described by [%alloc_pages_extframe].
- context register is zeroed.
- execution stack is affected in a non-trivial way (see step 10 in description for [%farcall]).

## Comparison with near calls

- Far calls can not accept more than [%max_passable] ergs, while near calls may accept all available ergs.
- Abnormal returns from far calls through [%OpPanic] or [%OpRevert] roll back all
storage changes that occured during the contract execution.

This includes exceptional situations when an error occured and the current
instruction is masked as [%OpPanic].


## Usage

- Calling other contracts
- Calling precompiles
  Usually we call a system contract with assigned precompile. It prepares data
  for a precompile, performs precompile call, and returns the result.

## Encoding

- In the encoding, [%OpDelegateCall], [%OpFarCall], and [%OpMimicCall] share the same opcode.


# Panics

1. Attempting to pass an existing [%fat_ptr], but the passed value is not tagged as a pointer.
 *)
  | farcall_fwd_existing_fatptr_notag: forall (ts1 ts2:transient_state) ___0 ___1 ___2 ___3 ___4 ___5,

     ts2 = ts1 <| gs_status := Panic FarCallInputIsNotPointerWhenExpected |> ->
     farcall
       ({|
           FarCall.fwd_memory   := ForwardExistingFatPointer ___0;
           ergs_passed          := ___1;
           FarCall.shard_id     := ___2;
           constructor_call     := ___3;
           to_system            := ___4;
         |},
         IntValue ___5) ts1 ts2
(** 2. The hash for the contract code (stored in the storage of [%DEPLOYER_SYSTEM_CONTRACT_ADDRESS]) is malformed. *)
  | farcall_malformed_decommitment_hash:  forall cs0 abi_shard is_syscall_query ts1 ts2 ___0 ___1 ___2 ___3 ___4,
      let is_system := addr_is_kernel dest && is_syscall_query in
      let allow_masking := negb is_system in
      let callee_shard := if is_shard_provided then abi_shard else current_shard cs0 in
      paid_code_fetch allow_masking callee_shard (gs_depot gs) (gs_contracts gs) dest cs0 (CodeFetchInvalidVerisonedHashFormat ___4) ->

      ts2 = ts1 <| gs_status := Panic FarCallInvalidCodeHashFormat |> ->
      farcall
        ({|
          FarCall.fwd_memory   := ___1;
          ergs_passed          := ___2;
          FarCall.shard_id     := abi_shard;
          constructor_call     := ___3;
          to_system            := is_syscall_query;
        |}, ___0)
       ts1 ts2
(** 3. Not enough ergs to pay for code decommitment. *)
  | farcall_decommitment_unaffordable:  forall cs0 abi_shard is_syscall_query ts1 ts2  ___1 ___2 ___3 ___4 ___5,
      let is_system := addr_is_kernel dest && is_syscall_query in
      let allow_masking := negb is_system in
      let callee_shard := if is_shard_provided then abi_shard else current_shard cs0 in
      paid_code_fetch allow_masking callee_shard (gs_depot gs) (gs_contracts gs) dest cs0 (CodeFetchUnaffordable ___1) ->
      cs0 = gs_callstack ts1 ->
      ts2 = ts1 <| gs_status := Panic FarCallNotEnoughErgsToDecommit |> ->
      farcall
        ({|
          FarCall.fwd_memory   := ___2;
          ergs_passed          := ___3;
          FarCall.shard_id     := abi_shard;
          constructor_call     := ___4;
          to_system            := is_syscall_query;
        |}, ___5)
       ts1 ts2
(** 4. Paid for decommitment; Returning a new fat pointer, but not enough ergs to pay for memory growth. *)
  | farcall_fwd_new_ptr_growth_unaffordable: forall cs0 cs1 ___1 ___2 ___3 abi_shard ergs_query is_syscall_query in_span page_type bound growth_query ts1 ts2,

      let is_system := addr_is_kernel dest && is_syscall_query in
      let allow_masking := negb is_system in
      let callee_shard := if is_shard_provided then abi_shard else current_shard cs0 in

      paid_code_fetch allow_masking callee_shard
        gs.(gs_revertable).(gs_depot) gs.(gs_contracts) dest cs0 (Fetched cs1 ___1 ___2) ->

      bound_of_span in_span page_type bound ->
      growth_to_bound bound cs1 growth_query ->
      affordable cs1 (cost_of_growth growth_query) = false ->

      cs0 = gs_callstack ts1 ->
      ts2 = ts1 <| gs_status := Panic FarCallNotEnoughErgsToGrowMemory |> ->
      farcall
        ({|
          FarCall.fwd_memory   := ForwardNewFatPointer page_type in_span;
          ergs_passed          := ergs_query;
          FarCall.shard_id     := abi_shard;
          constructor_call     := false;
          to_system            := is_syscall_query;
          |}, ___3)
       ts1 ts2
  .
(** ## Not formalized
- system contracts + constructor calls + "call in now constructed system contract" exception
 *)
End FarCallDefinitions.

Inductive step_farcall : instruction -> smallstep :=

| step_farcall_normal: forall handler abi abi_enc (dest:word) call_shard call_as_static s1 s2 ts1 ts2 (__:bool),

    let dest_addr := low contract_address_bits dest in
    let handler_code_addr := low code_address_bits handler in
    farcall Normal call_as_static call_shard dest_addr handler_code_addr s1.(gs_global) (abi,abi_enc) ts1 ts2  ->
    step_transient_only ts1 ts2 s1 s2 ->
    step_farcall (OpFarCall (Some abi, abi_enc) (mk_pv __ dest) handler call_shard call_as_static) s1 s2
| step_farcall_mimic: forall handler abi abi_enc (dest:word) call_shard call_as_static s1 s2 ts1 ts2 (__:bool),

    let dest_addr := low contract_address_bits dest in
    let handler_code_addr := low code_address_bits handler in
    farcall Mimic call_as_static call_shard dest_addr handler_code_addr s1.(gs_global) (abi,abi_enc) ts1 ts2  ->
    step_transient_only ts1 ts2 s1 s2 ->
    step_farcall (OpMimicCall (Some abi, abi_enc) (mk_pv __ dest) handler call_shard call_as_static) s1 s2
| step_farcall_delegate: forall handler abi abi_enc (dest:word) call_shard call_as_static s1 s2 ts1 ts2 (__:bool),

    let dest_addr := low contract_address_bits dest in
    let handler_code_addr := low code_address_bits handler in
    farcall Delegate call_as_static call_shard dest_addr handler_code_addr s1.(gs_global) (abi,abi_enc) ts1 ts2  ->
    step_transient_only ts1 ts2 s1 s2 ->
    step_farcall (OpDelegateCall (Some abi, abi_enc) (mk_pv __ dest) handler call_shard call_as_static) s1 s2
.
