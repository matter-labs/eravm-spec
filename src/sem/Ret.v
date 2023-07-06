From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Coder Common Condition CallStack GPR Memory MemoryOps Instruction State ZMod
  ABI ABI.FarRet ABI.FatPointer Addressing.Coercions Pointer PrimitiveValue SemanticCommon RecordSetNotations MemoryContext.
(**
# Returns

These three instructions return control from a currently executing function:



- `ret`
- `revert`
- `panic`


Their semantic changes semantics depending on whether the current frame is
external or internal.


Reminder: *callee* is the function that we call; the *caller* is the currently
executing function where a call takes place. In other words, the caller calls
the callee.

*)
Generalizable Variables regs flags pages s.
Inductive step_ret: instruction -> xsmallstep :=
(**

## `ret` (normal return, not panic/revert)

### Abstract Syntax

- [OpRet (args: in_reg) (label: option code_address)]

### Syntax

- `ret`

  A normal return from a **near** call. Will pop up current callframe, give back unspent ergs and
  continue execution from the saved return address (from where the call had taken place).


- `ret label`

  A normal return from a **near** call. Will pop up current callframe, give back unspent ergs and
  continue execution from an explicitly provided label.

- `ret abi_reg`

  A normal return from a **far** call. Will pop up current callframe, give back unspent ergs and
  continue execution from the saved return address (from where the call had taken place).
  The register `abi_reg` describes a slice of memory passed to the external caller.

  The assembler expands `ret` to `ret r1`, but `r1` is ignored by returns from near calls.


### Semantic

#### Common notes

- `ret` always clears flags.
- returns from far calls ignore an explicit label from the instruction.
- returns from far calls may pass data to the caller in form of a fat pointer.

#### Case 1: `ret` from near call, no label

1. Pass all ergs from the current frame to the parent frame.
2. Drop current frame.
3. Clear flags

 *)
| step_NearRet:
    forall cf caller_stack caller_reimbursed,
      `(
      ergs_reimburse_caller_and_drop (InternalCall cf caller_stack) caller_reimbursed ->

       step_ret OpNearRet {|
          gs_flags        := flags;
          gs_callstack    := InternalCall cf caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := caller_reimbursed;


          gs_regs         := regs;
          gs_pages        := pages;
        |}
        )
(**

#### Case 2: `ret label` from local call, label provided.

1. Pass all ergs from the current frame to the parent frame.
2. Drop current frame.
3. Clear flags
4. Set PC to the label value.

*)

| step_NearRetTo:
    forall cf caller_stack caller_reimbursed label,
      `(
      ergs_reimburse_caller_and_drop (InternalCall cf caller_stack) caller_reimbursed ->

      step_ret (OpNearRetTo label) {|
          gs_flags        := flags;
          gs_callstack    := InternalCall cf caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := pc_set label caller_reimbursed;


          gs_regs         := regs;
          gs_pages        := pages;
        |}
        )
.
Open Scope ZMod_scope.
Generalizable Variables cs.

Inductive step_retext : instruction -> smallstep :=
(**

#### Case 3: `ret abi_reg` from external call

1. Fetch the value from register `abi_reg` and decode the following structure `params` (see `Ret.ABI`):

```
Inductive forward_page_type := UseHeap | ForwardFatPointer | UseAuxHeap.

Record fat_ptr := {
   fp_page:   option page_id;
   fp_start:  mem_address;
   fp_length: mem_address;
   fp_offset: mem_address;
}.
Record params := {
   memory_quasi_fat_ptr: fat_ptr;
   page_forwarding_mode: forward_page_type;
}.
```

2. Forward a memory slice to the caller (see [paid_forward]):
   - If `page_forwarding_mode` is `ForwardFatPointer`, then:
      + ensure that the register containing `abi_reg`  is tagged as pointer.
      + ensure that `memory_quasi_fat_ptr` does NOT refer to a page owned by an older frame.
      + shrink `memory_quasi_fat_ptr` so it starts at its current offset, and the offset is reset to zero.

        TODO Explanation why the circularity check is necessary.

   - Otherwise, if `page_forwarding_mode` is `UseHeap` or `UseAuxHeap`, then:
      + overwrite the page ID in `memory_quasi_fat_ptr` with current frame's heap or auxheap page ID.
      + if the upper bound `(fp_start + fp_length)` of `memory_quasi_fat_ptr` is
         out of heap/auxheap bounds, pay for the growth difference.

     Note: it is not useful to readjust the current heap/auxheap bounds after
     paying for growth. The bounds are stored in the current callframe which is
     about to be discarded.

3. Pass the remaining ergs back to the caller.
4. Clear flags.
5. Encode the modified (through the step 2) `memory_quasi_fat_ptr` and put it to `R1` with pointer tag.

All other registers are zeroed. Registers `R2`, `R3` and `R4` are reserved and may gain a special meaning in newer versions of EraVM.
6. Context register is zeroed.


*)
| step_RetExt_heapvar:
  forall gs pages cf caller_stack cs1 caller_reimbursed ___ regs (arg:in_reg) heap_span_enc out_ptr ____ heap_type hspan,
    let cs0 := ExternalCall cf (Some caller_stack) in

    load_reg_any regs arg heap_span_enc ->

    decode FarRet.ABI heap_span_enc = Some (ForwardNewHeapPointer heap_type hspan) ->

    paid_forward_heap_span heap_type (hspan, cs0) (out_ptr, cs1) ->
    ergs_reimburse_caller_and_drop cs1 caller_reimbursed ->

    step_retext (OpFarRet arg)
          {|
            gs_xstate := {|
                          gs_flags        := ___ ;
                          gs_callstack    := cs0;
                          gs_regs         := regs;


                          gs_pages        := pages;
                        |};
            gs_context_u128 := ____;

            gs_global       := gs;
          |}
          {|
            gs_xstate := {|
                          gs_flags        := flags_clear;
                          gs_callstack    := caller_reimbursed;
                          gs_regs         := regs_state_zero
                             <| r1 := PtrValue (encode FatPointer.ABI out_ptr) |>
                             <| r2 := reserved |>
                             <| r3 := reserved |>
                             <| r4 := reserved |> ;


                          gs_pages        := pages;
                          |};


          gs_context_u128 := zero128;

          gs_global       := gs;
          |}
| step_RetExt_ForwardFatPointer:
  forall __ gs pages cf caller_stack cs1 caller_reimbursed ___ regs (arg:in_reg) in_ptr_encoded in_ptr out_ptr page,
    let cs0 := ExternalCall cf (Some caller_stack) in

    (* Panic if not a pointer *)
    load_reg regs arg (PtrValue in_ptr_encoded) ->

    FarRet.ABI.(decode) in_ptr_encoded = Some (ForwardFatPointer in_ptr) ->
    in_ptr.(fp_page) = Some page ->

    negb ( page_older page (get_mem_ctx cs0)) = true ->

    validate in_ptr = no_exceptions ->

    fp_shrink in_ptr out_ptr ->

    ergs_reimburse_caller_and_drop cs1 caller_reimbursed ->

    step_retext (OpFarRet arg)
          {|
            gs_xstate := {|
                          gs_flags        := __ ;
                          gs_callstack    := cs0;
                          gs_regs         := regs;


                          gs_pages        := pages;
                        |};
            gs_context_u128 := ___;

            gs_global       := gs;
          |}
          {|
            gs_xstate := {|
                          gs_flags        := flags_clear;
                          gs_callstack    := caller_reimbursed;
                          gs_regs         := regs_state_zero
                             <| r1 := PtrValue (FatPointer.ABI.(encode) out_ptr) |>
                             <| r2 := reserved |>
                             <| r3 := reserved |>
                             <| r4 := reserved |> ;


                          gs_pages        := pages;
                          |};


          gs_context_u128 := zero128;

          gs_global       := gs;
          |}
.

(**

### Affected parts of VM state

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

### Usage

### Similar instructions

- `revert` executes the current frame's exception handler instead of returning
  to the caller.
- `panic` executes the current frame's exception handler instead of returning to
  the caller, and sets overflow flag.


*)

