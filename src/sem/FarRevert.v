From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Coder Common Flags CallStack GPR Memory MemoryOps isa.CoreSet State ZMod
  ABI ABI.FarRet ABI.FatPointer Addressing.Coercions Pointer PrimitiveValue SemanticCommon RecordSetNotations.

Inductive step_farrevert: instruction -> smallstep :=

(** ## Far revert (return with recoverable error)

Return from a function signaling an error; execute exception handler, possibly
return data like normal `ret`.

### Abstract Syntax

[%OpFarRevert (args: in_reg)]

### Syntax

`revert abi_reg`

An abnormal return from a **far** call. Will pop up current callframe, give back
unspent ergs and execute a currently active exception handler. The register
`abi_reg` describes a slice of memory passed to the external caller.

Restores storage to the state before external call.

The assembler expands `revert` to `revert r1`, but `r1` is ignored by reverts from near calls.

### Semantic

Effectively the same as `ret abi_reg`, but restores storage and executes the exception handler.

1. Perform a [%rollback].
2. Fetch the value from register `abi_reg` and decode the value of type [%fwd_memory]:

```
Inductive fwd_memory :=
  ForwardFatPointer (p:fat_ptr)
| ForwardNewHeapPointer (heap_var: data_page_type) (s:span).
```

   The exact encoding is described by ABI.

3. Forward a memory span to the caller (see [%paid_forward_heap_span]):
   - For [%ForwardFatPointer p]:
      + ensure that the register containing `abi_reg`  is tagged as pointer.
      + ensure that the memory page of `p` does NOT refer to a page owned by an older frame.
      + [%fp_narrow] [%p] so it starts at its current offset, and the offset is reset to zero. See [%free_ptr_narrow].

        TODO Explanation why the circularity check is necessary.

     There is no payment because the existing fat pointer has already been paid for

   - For [%ForwardNewHeapPointer heap_var (start, limit)]:
      + let $B$ be the bound of the heap variant [%heap_var] taken from
        [%ctx_heap_bound] field of [%ecf_mem_ctx] of the active external frame.
      + let $I$ be the page id of the heap variant [%heap_var] taken from
        [%ctx_heap_page_id] field of [%ecf_mem_ctx] of the active external frame.
      + form a fat pointer $P$ from the span as described in
        [%paid_forward_heap_span].

         $$P := (I, (\mathit{addr}, \mathit{length}), 0)$$

      + if $\mathit{start} + \mathit{limit} >B$, pay for the growth difference
        [%Ergs.growth_cost] $(\mathit{start} + \mathit{limit} - B)$.

     Note: it is not useful to readjust the current heap/auxheap bounds after
     paying for growth. The bounds are part of [%mem_ctx] of the topmost frame, which is about to be discarded.

4. Return the remaining ergs to the caller.
5. Clear flags.
6. Encode $P$ and store it in register [%r1], setting its pointer tag.

   All other registers are zeroed. Registers [%r2], [%r3], and [%r4] are
   reserved and may gain a special meaning in newer versions of EraVM.
 7. Context register is zeroed.
*)
| step_RevertExt_heapvar:
  forall gs gs' pages cf caller_stack cs1 new_caller params out_ptr heap_type hspan __ ___ ____ _____,
    let cs0 := ExternalCall cf (Some caller_stack) in

    params = ForwardNewHeapPointer heap_type hspan ->

    paid_forward_heap_span heap_type (hspan, cs0) (out_ptr, cs1) ->
    ergs_return_caller_and_drop cs1 new_caller ->

    rollback cf.(cf_saved_checkpoint) gs gs' ->
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
                          gs_regs         := regs_state_zero
                             <| r1 := PtrValue (encode FatPointer.ABI out_ptr) |>
                             <| r2 := reserved |>
                             <| r3 := reserved |>
                             <| r4 := reserved |> ;
                          gs_context_u128 := zero128;

                          gs_pages        := pages;
                          |};
          gs_global       := gs';
          |}
| step_RevertExt_ForwardFatPointer:
  forall pages cf caller_stack cs1 new_caller __ ___ ____ _____ in_ptr out_ptr page params gs gs',
    let cs0 := ExternalCall cf (Some caller_stack) in

    (* Panic if not a pointer *)

    params = ForwardFatPointer in_ptr ->
    in_ptr.(fp_page) = Some page ->

    MemoryContext.page_older page (get_mem_ctx cs0) = false ->

    validate in_ptr = no_exceptions ->

    fat_ptr_narrow in_ptr out_ptr ->

    ergs_return_caller_and_drop cs1 new_caller ->

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
                          gs_regs         := regs_state_zero
                             <| r1 := PtrValue (FatPointer.ABI.(encode) out_ptr) |>
                             <| r2 := reserved |>
                             <| r3 := reserved |>
                             <| r4 := reserved |> ;
                          gs_context_u128 := zero128;

                          gs_pages        := pages;
                          |};

          gs_global       := gs';
          |}
.
(** ### Affected parts of VM state

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

### Usage

- Abnormal returns from near/far calls when a recoverable error happened.
Use `panic` for irrecoverable errors.

### Similar instructions

- `ret` returns to the caller instead of executing an exception handler.
- `panic` acts similar to `revert` but does not let pass any data to the caller
  and sets an overflow flag, and burns ergs in current frame. *)
