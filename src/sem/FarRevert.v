From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Coder Common Flags CallStack GPR Memory MemoryOps isa.CoreSet State ZMod
  ABI ABI.FarRet ABI.FatPointer Addressing.Coercions Pointer PrimitiveValue SemanticCommon RecordSetNotations.

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
    forall gs gs' pages cf caller_stack cs1 cs2 new_caller new_regs params out_ptr heap_type hspan __ ___ ____ _____,
      let cs0 := ExternalCall cf (Some caller_stack) in

      params = ForwardNewFatPointer heap_type hspan ->

      paid_forward_heap_span heap_type (hspan, cs0) (out_ptr, cs1) ->
      ergs_return_caller_and_drop cs1 cs2 ->

      new_caller = pc_set (active_exception_handler cs0) cs2 ->
      
      rollback cf.(cf_saved_checkpoint) gs gs' ->
      new_regs = reserve (regs_state_zero <| r1 := PtrValue (encode FatPointer.ABI out_ptr) |> )->

      step_farrevert (OpFarRevert (Some (FarRet.mk_params params), _____))
                     {|
                       gs_transient := {|
                                        gs_flags        := __ ;
                                        gs_callstack    := cs0;
                                        gs_regs         := ___;
                                        gs_context_u128 := ____;

                                        gs_pages        := pages;
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
                                      |};
                       gs_global       := gs';
                     |}
  | step_RevertExt_ForwardFatPointer:
    forall pages cf caller_stack cs1 cs2 new_caller new_regs __ ___ ____ _____ in_ptr out_ptr page params gs gs',
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
      step_farrevert (OpFarRevert (Some (FarRet.mk_params params), _____))
                     {|
                       gs_transient := {|
                                        gs_flags        := __ ;
                                        gs_callstack    := cs0;
                                        gs_regs         := ___ ;
                                        gs_context_u128 := ____;

                                        gs_pages        := pages;
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
                                      |};

                       gs_global       := gs';
                     |}
  .
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
  and sets an overflow flag, and burns ergs in current frame. *)
End FarRevertDefinition.
