From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Coder Common Condition CallStack GPR Memory MemoryOps Instruction State ZMod
  ABI ABI.Ret ABI.FatPointer Addressing.Coercions Pointer PrimitiveValue SemanticCommon RecordSetNotations.
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

Generalizable Variables cs.
Inductive step_retext : instruction -> smallstep :=
(**

#### Case 3: `ret abi_reg` from external call

1. Fetch the value from register `abi_reg` and decode the following structure `params` (see `Ret.ABI`):

```
Inductive forward_page_type := UseHeap | ForwardFatPointer | UseAuxHeap.

Record fat_ptr := {
   fp_page:   page_id;
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
| step_RetExt:
  forall __ gs pages cf caller_stack cs1 caller_reimbursed ___ regs (arg:in_reg) in_ptr_encoded in_ptr fwd_mode abi_ptr_tag out_ptr page,
    let cs0 := ExternalCall cf (Some caller_stack) in
    
    (* Panic if not a pointer *)
    load_reg regs arg (mk_pv abi_ptr_tag in_ptr_encoded) ->

    Ret.ABI.(decode) in_ptr_encoded = Some (Ret.mk_params in_ptr fwd_mode) ->
    in_ptr.(fp_page) = Some page ->
    (fwd_mode = ForwardFatPointer -> abi_ptr_tag && negb ( MemoryContext.page_older page (get_mem_ctx cs0)) = true) ->

    paid_forward fwd_mode (in_ptr, cs0) (out_ptr, cs1) ->
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
- Normal returns from near calls.
- Normal returns from far calls.

### Similar instructions

- `revert` executes the current frame's exception handler instead of returning
  to the caller.
- `panic` executes the current frame's exception handler instead of returning to
  the caller, and sets overflow flag.


*)

Inductive step_revert: instruction -> xsmallstep :=
(**

## `revert` (recoverable error, not normal return/not panic)

Return from a function signaling an error; execute exception handler, possibly return data like normal `ret`.

### Abstract Syntax

- [OpRevert (args: in_reg) (label: option code_address)]

### Syntax

- `revert`

  An abnormal return from a **near** call. Will pop up current callframe, give back unspent ergs and
  pass control to the current exception handler.


- `revert label`

  An abnormal return from a **near** call. Will pop up current callframe, give back unspent ergs and
  continue execution from an explicitly provided label.

- `revert abi_reg`

  An abnormal return from a **far** call. Will pop up current callframe, give back unspent ergs and
  execute a currently active exception handler.
  The register `abi_reg` describes a slice of memory passed to the external caller.

  Restores storage to the state before external call.

  The assembler expands `revert` to `revert r1`, but `r1` is ignored by reverts from near calls.
  

### Semantic

#### Common notes

- `revert` always clears flags.
- reverts from far calls ignore an explicit label from the instruction.
- reverts from far calls may pass data to the caller in form of a fat pointer.

#### Case 1: `revert` from near call, no label

1. Pass all ergs from the current frame to the parent frame.
2. Drop current frame. 
3. Set PC to the exception handler of a dropped frame.
4. Clear flags

 *)
| step_RevertLocal_nolabel:
    forall flags pages cf caller_stack caller_reimbursed regs ,

      ergs_reimburse_caller_and_drop (InternalCall cf caller_stack) caller_reimbursed ->
      let handler := active_exception_handler (InternalCall cf caller_stack) in

      step_revert OpNearRevert {|
          gs_flags        := flags;
          gs_callstack    := InternalCall cf caller_stack;
          
          
          gs_regs         := regs;
          gs_pages        := pages;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := pc_set handler caller_reimbursed;


          gs_regs         := regs;
          gs_pages        := pages;

        |}
        (**

#### Case 2: `revert label` from near call, label provided

1. Pass all ergs from the current frame to the parent frame.
2. Drop current frame. 
3. Set PC to the label provided
4. Clear flags

*)
| step_RevertLocal_label:
    forall flags pages cf caller_stack caller_reimbursed regs label,

      ergs_reimburse_caller_and_drop (InternalCall cf caller_stack) caller_reimbursed ->
      
      step_revert (OpNearRevertTo label) {|
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

.
Inductive step_revertext: instruction -> smallstep :=
(**

#### Case 3: `revert abi_reg` from external call

Effectively the same as `ret abi_reg`, but restores storage and executes the exception handler.

1. Fetch the value from register `abi_reg` and decode the following structure `params` (see `Ret.ABI`):

```
Inductive forward_page_type := UseHeap | ForwardFatPointer | UseAuxHeap.

Record fat_ptr := {
   fp_page:   page_id;
   fp_start:  mem_address;
   fp_length: mem_address;
   fp_offset: mem_address;
}.
Record params := {
   memory_quasi_fat_ptr: fat_ptr;
   page_forwarding_mode: forward_page_type;
}.
```

2. Forward a memory slice to the caller:
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
7. All storages are reverted to the state prior to the current contract call.

*)
| step_RevertExt:
   forall __ pages cf caller_stack cs1 caller_reimbursed ___ regs (arg:in_reg) in_ptr_encoded in_ptr fwd_mode abi_ptr_tag out_ptr page tx_num codes cergs rev,
     let cs0 := ExternalCall cf (Some caller_stack) in
    
    (* Panic if not a pointer *)
    load_reg regs arg (mk_pv abi_ptr_tag in_ptr_encoded) ->

    Ret.ABI.(decode) in_ptr_encoded = Some (Ret.mk_params in_ptr fwd_mode) ->
    in_ptr.(fp_page) = Some page ->
    (fwd_mode = ForwardFatPointer -> abi_ptr_tag && negb ( MemoryContext.page_older page (get_mem_ctx cs0)) = true) ->

    paid_forward fwd_mode (in_ptr, cs0) (out_ptr, cs1) ->
    ergs_reimburse_caller_and_drop cs1 caller_reimbursed ->

    step_revertext (OpFarRevert arg)
          {|
            gs_xstate := {|
                          gs_flags        := __;
                          gs_callstack    := cs0;
                          gs_regs         := regs;

                          
                          gs_pages        := pages;
                        |};
            gs_context_u128 := ___;
            
            gs_global       := {|
                              gs_current_ergs_per_pubdata_byte := cergs;
                              gs_tx_number_in_block := tx_num;
                              gs_contracts := codes;
                              gs_revertable := rev;
                            |};
          |}
          {|
            gs_xstate := {|
                          gs_flags        := flags_clear;
                          gs_regs         := regs_state_zero
                             <| r1 := PtrValue (FatPointer.ABI.(encode) out_ptr) |>
                             <| r2 := reserved |>
                             <| r3 := reserved |>
                             <| r4 := reserved |> ;
                          gs_callstack    := pc_set (active_exception_handler cs0) caller_reimbursed ;

                          gs_pages        := pages;
                          |};

                          
          gs_context_u128 := zero128;

          gs_global       := {|
                              gs_current_ergs_per_pubdata_byte := cergs;
                              gs_tx_number_in_block := tx_num;
                              gs_contracts := codes;
                              gs_revertable := revert_state cf;
                            |}
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
- Storage changes are reverted.
 
### Usage

- Abnormal returns from near/far calls when a recoverable error happened.
Use `panic` for irrecoverable errors.

### Similar instructions

- `ret` returns to the caller instead of executing an exception handler.
- `panic` acts similar to `revert` but does not let pass any data to the caller
  and sets an overflow flag, and burns ergs in current frame.


*)

Inductive step_panic: instruction -> xsmallstep :=
(**
## `panic` (irrecoverable error, not normal return/not return from recoverable error)

Return from a function signaling an error; execute exception handler, burn all
regs in current frame, set OF flag, return no data.

### Abstract Syntax

- [OpPanic (args: in_reg) (label: option code_address)]

### Syntax

- `panic` (when current call is internal)

  An abnormal return from a **near** call. Will pop up current callframe, burn all ergs and
  pass control to the current exception handler, setting OF flag.


- `panic label` (when current call is internal)

  An abnormal return from a **near** call. Will pop up current callframe, burn all ergs and
  pass control to the current exception handler, setting OF flag.

- `panic` (when current call is external)

  An abnormal return from a **far** call. Will pop up current callframe, burn all ergs and
  execute a current exception handler, setting OF flag.

  Restores storage to the state before external call.

  The assembler expands `panic` to `panicr1`, but `r1` is ignored by returns from near calls.
  

### Semantic

#### Common notes

- `panic` always clears flags and sets OF.
- panics from far calls ignore an explicit label from the instruction.
- panic can't pass data to caller.
- most errors in executing of other instructions lead to executing `panic` instead.


#### Case 1: `panic` from near call, no label

1. Drop current frame with its ergs.
2. Set PC to the exception handler of a dropped frame.
3. Clear flags, and set OF.

 *)


| step_PanicLocal_nolabel:
    forall flags pages cf caller_stack regs,

      (* no reimbursement, ergs are lost *)
      let handler := active_exception_handler (InternalCall cf caller_stack) in
      
      step_panic OpPanic {|
          gs_flags        := flags;
          gs_callstack    := InternalCall cf caller_stack;
          
          gs_regs         := regs;
          gs_pages        := pages;
          |}
          {|
          gs_flags        := set_overflow flags_clear;
          gs_callstack    := pc_set handler caller_stack;

          gs_regs         := regs;
          gs_pages        := pages;
          |} 
        (**

#### Case 2: `panic` from near call, label provided

1. Drop current frame with its ergs.
2. Set PC to label value.
3. Clear flags, and set OF.

 *)
| step_PanicLocal_label:
    forall __ pages ___ caller_stack regs label,

      step_panic (OpNearPanicTo label)
        {|
          gs_flags        := __;
          gs_callstack    := InternalCall ___ caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
        |}
        {|
          gs_flags        := set_overflow flags_clear;
          gs_callstack    := pc_set label caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
        |}
     .

     Inductive step_farpanic : instruction -> smallstep :=
(**

#### Case 3: `revert` from external call

1. Drop current frame and its ergs
2. Clear flags and set OF.
3. Clear context register.
4. Set PC to the exception handler address of a dropped frame.
5. All storages are reverted to the state prior to the current contract call.
6. Context register is zeroed.
7. Put an encoded zero-pointer into `R1` and tag `R1` as a pointer.

   All other registers are zeroed. Registers `R2`, `R3` and `R4` are reserved
   and may gain a special meaning in newer versions of EraVM.

*)
| step_PanicExt:
  forall codes flags rev pages cf caller_stack context_u128 regs (arg:in_reg) cergs tx_num,
    let cs0 := ExternalCall cf (Some caller_stack) in

    let encoded_out_ptr := FatPointer.ABI.(encode) fat_ptr_empty in
    step_farpanic OpPanic
          {|
            gs_xstate := {|
                          gs_flags        := flags;
                          gs_callstack    := cs0;
                          gs_regs         := regs;

                          
                          gs_pages        := pages;
                        |};
            gs_context_u128 := context_u128;
            
            gs_global       := {|
                              gs_current_ergs_per_pubdata_byte := cergs;
                              gs_tx_number_in_block := tx_num;
                              gs_contracts := codes;
                              gs_revertable := rev;
                            |};
          |}
          {|
            gs_xstate := {|
                          gs_flags        := set_overflow flags_clear;
                          gs_regs         := regs_state_zero
                             <| r1 := PtrValue encoded_out_ptr |>
                             <| r2 := reserved |>
                             <| r3 := reserved |>
                             <| r4 := reserved |> ;
                          gs_callstack    := pc_set (active_exception_handler cs0) caller_stack;

                          gs_pages        := pages;
                          |};

                          
          gs_context_u128 := zero128;

          gs_global       := {|
                              gs_current_ergs_per_pubdata_byte := cergs;
                              gs_tx_number_in_block := tx_num;
                              gs_contracts := codes;
                              gs_revertable := revert_state cf;
                            |}
          |}

.
(**

### Affected parts of VM state

- Flags are cleared, then OF is set.
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

- Abnormal returns from near/far calls when an irrecoverable error has happened.
Use `revert` for recoverable errors.
- An attempt of executing an invalid instruction will result in executing `panic`.
- Most error situations happening during execution will result in executing `panic`.

### Similar instructions

- `ret` returns to the caller instead of executing an exception handler, and does not burn ergs.
- `revert` acts similar to `panic` but does not burn ergs and lets pass any data to the caller, and does not set an overflow flag.


*)
