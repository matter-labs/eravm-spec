From RecordUpdate Require Import RecordSet.

Require
ABI
Bool
CallStack
Coder
Common
Flags
GPR
MemoryContext
MemoryManagement
Pointer
PrimitiveValue
SemanticCommon
State.

Import
ABI
ABI.FatPointer
Bool
CallStack
Coder
Common
Flags
GPR
isa.CoreSet
MemoryContext
MemoryManagement
Pointer
PrimitiveValue
RecordSetNotations
SemanticCommon
State
StepPanic
.

Section FarRevertDefinition.

  Let reserve regs :=
   regs    <| r2 := reserved |> <| r3 := reserved |> <| r4 := reserved |>.

  Inductive step_farrevert: instruction -> smallstep :=
  (** # Far revert (return from recoverable error, not panic/normal return)

## Abstract Syntax

[%OpFarRevert (args: in_reg)]

## Syntax

`ret.revert in1` aliased as `revert in1`

An abnormal return from a far call. Will pop up current callframe, give back
unspent ergs and execute a currently active exception handler. The register
abi_reg describes a slice of memory passed to the external caller.

Restores storage to the state before external call.

The assembler expands `revert` to `revert r1`; `r1` is ignored by returns from
near calls.

## Semantic

1. Let $E$ be the address of the [%active_exception_handler].
2. Perform a [%rollback].
3. Proceed with the same steps as [%OpFarRet] (see [%step_farret]).
3. Set PC to $E$.
   *)
  | step_RevertExt_heapvar:
    forall gs gs' pages cf caller_stack cs1 cs2 new_caller new_regs params out_ptr heap_type hspan ___1 ___2 ___3 ___4,
      let cs0 := ExternalCall cf (Some caller_stack) in

      params = ForwardNewFatPointer heap_type hspan ->

      paid_forward_new_fat_ptr heap_type hspan cs0 (out_ptr, cs1) ->
      ergs_return_caller_and_drop cs1 cs2 ->

      new_caller = pc_set (active_exception_handler cs0) cs2 ->

      rollback cf.(cf_saved_checkpoint) gs gs' ->
      new_regs = reserve (regs_state_zero <| r1 := PtrValue (encode FatPointer.ABI out_ptr) |> )->

      step_farrevert (OpFarRevert (Some (FarRet.mk_params params), ___1))
                     {|
                       gs_transient := {|
                                        gs_flags        := ___2 ;
                                        gs_callstack    := cs0;
                                        gs_regs         := ___3;
                                        gs_context_u128 := ___4;

                                        gs_pages        := pages;
                                        gs_status       := NoPanic;
                                      |};
                       gs_global       := gs;
                     |}
                     {|
                       gs_transient := {|
                                        gs_flags        := flags_clear;
                                        gs_callstack    := new_caller;
                                        gs_regs         := new_regs;
                                        gs_context_u128 := zero128;

                                        gs_pages        := pages;
                                        gs_status       := NoPanic;
                                      |};
                       gs_global       := gs';
                     |}
  | step_RevertExt_ForwardFatPointer:
    forall pages cf caller_stack cs1 cs2 new_caller new_regs ___1 ___2 ___3 ___4 in_ptr out_ptr page params gs gs',
      let cs0 := ExternalCall cf (Some caller_stack) in

      (* Panic if not a pointer *)

      params = ForwardExistingFatPointer in_ptr ->
      in_ptr.(fp_page) = Some page ->

      MemoryContext.page_older page (get_mem_ctx cs0) = false ->

      validate in_ptr = no_exceptions ->

      fat_ptr_narrow in_ptr out_ptr ->

      ergs_return_caller_and_drop cs1 cs2 ->

      new_caller = pc_set (active_exception_handler cs0) cs2 ->
      new_regs = (reserve regs_state_zero) <| r1 := PtrValue (FatPointer.ABI.(encode) out_ptr) |> ->
      rollback cf.(cf_saved_checkpoint) gs gs' ->
      step_farrevert (OpFarRevert (Some (FarRet.mk_params params), ___1))
                     {|
                       gs_transient := {|
                                        gs_flags        := ___2;
                                        gs_callstack    := cs0;
                                        gs_regs         := ___3 ;
                                        gs_context_u128 := ___4;

                                        gs_pages        := pages;
                                        gs_status       := NoPanic;
                                      |};

                       gs_global       := gs;
                     |}
                     {|
                       gs_transient := {|
                                        gs_flags        := flags_clear;
                                        gs_callstack    := new_caller;
                                        gs_regs         := new_regs;
                                        gs_context_u128 := zero128;

                                        gs_pages        := pages;
                                        gs_status       := NoPanic;
                                      |};

                       gs_global       := gs';
                     |}

(** ## Affected parts of VM state

- Flags are cleared.
- Context register is zeroed (only returns from far calls).
- Registers are cleared (only returns from far calls).
- Execution stack:
  + Current frame is dropped.
  + Caller frame:
    * if a label is explicitly provided, and current frame is internal (near
      call), then caller's PC is overwritten with the label. Returns from
      external calls ignore label, even if it is explicitly provided.
    * Unspent ergs are given back to caller (but memory growth is paid first).
- Storage changes are reverted.

## Usage

- Abnormal returns from near/far calls when a recoverable error happened.
Use `panic` for irrecoverable errors.

## Similar instructions

- `ret` returns to the caller instead of executing an exception handler.
- `panic` acts similar to `revert` but does not let pass any data to the caller
  and sets an overflow flag, and burns ergs in current frame.



## Panics

1. Attempt to forward an existing fat pointer, but the value holding [%ABI.Ret.params] is not tagged as a pointer.
*)

  | step_RevertExt_ForwardFatPointer_requires_ptrtag:
  forall cf caller_stack __ params ___1 (s1 s2:state),
    let cs0 := ExternalCall cf (Some caller_stack) in
    gs_callstack s1 = cs0 ->
    params = FarRet.mk_params (ForwardExistingFatPointer __) ->
    step_panic
      RetABIExistingFatPointerWithoutTag
      s1 s2 ->
    step_farrevert (OpFarRevert (Some params, IntValue ___1)) s1 s2

(** 2. Attempt to return a pointer created before the current callframe.
It is forbidden to pass a pointer to a contract in a far call and return it back.
Otherwise we could create a [%fat_ptr] $P$ to a heap page of contract $A$, pass it to a contract $B$, return it back to $A$, and then modify the contents on the heap page of $A$. This way we will also modify the memory [%slice] associated with $P$.

In other words, this is a situation where:

- caller makes far call to some contract;
- callee does return-forward @calldataptr;
- caller modifies calldata corresponding heap region, that leads to modification of returndata.

*)
  | step_RevertExt_ForwardFatPointer_returning_older_pointer:
  forall cf caller_stack ___1 in_ptr page params (s1 s2:state) ,
    let cs0 := ExternalCall cf (Some caller_stack) in
    gs_callstack s1 = cs0 ->

    in_ptr.(fp_page) = Some page ->

    page_older page (get_mem_ctx cs0) = true ->
    params = FarRet.mk_params (ForwardExistingFatPointer in_ptr) ->
    step_panic
      RetABIReturnsPointerCreatedByCaller
      s1 s2 ->
    step_farrevert (OpFarRevert (Some params, ___1)) s1 s2
(** 3. Attempt to return a malformed pointer. *)
  | step_RevertExt_ForwardFatPointer_returning_malformed_pointer:
  forall cf caller_stack ___1 (in_ptr: fat_ptr) params (s1 s2:state) ,
    let cs0 := ExternalCall cf (Some caller_stack) in
    gs_callstack s1 = cs0 ->

    validate in_ptr <> no_exceptions ->

    params = FarRet.mk_params (ForwardExistingFatPointer in_ptr) ->
    step_panic
      FatPointerMalformed
      s1 s2 ->
    step_farrevert (OpFarRevert (Some params, ___1)) s1 s2
(** 4. Attempt to return a new pointer but unable to pay for memory growth. *)
| step_RevertExt_heapvar_growth_unaffordable:
  forall cf caller_stack __ heap_type hspan params (s1 s2:state),
    let cs0 := ExternalCall cf (Some caller_stack) in
    gs_callstack s1 = cs0 ->
    params = FarRet.mk_params (ForwardNewFatPointer heap_type hspan) ->
    growth_to_span_unaffordable cs0 heap_type hspan ->
    step_panic
      FatPointerCreationUnaffordable
      s1 s2 ->
    step_farrevert (OpFarRevert (Some params, __)) s1 s2.

End FarRevertDefinition.
