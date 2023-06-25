From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Common Condition CallStack Memory MemoryOps Instruction State ZMod
  ABI ABI.Ret ABI.FatPointer Addressing.Coercions SemanticCommon RecordSetNotations.
        

Inductive step_revert: instruction -> smallstep :=
(**

# `revert` (recoverable error, not normal return/not panic)

Return from a function signaling an error; execute exception handler, possibly return data like normal `ret`.

## Abstract Syntax

- [OpRevert (args: in_reg) (label: option code_address)]

## Syntax

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
  

## Semantic

### Common notes

- `revert` always clears flags.
- reverts from far calls ignore an explicit label from the instruction.
- reverts from far calls may pass data to the caller in form of a fat pointer.

### Case 1: `revert` from near call, no label

1. Pass all ergs from the current frame to the parent frame.
2. Drop current frame. 
3. Set PC to the exception handler of a dropped frame.
4. Clear flags

 *)
| step_RevertLocal_nolabel:
    forall flags pages cf caller_stack caller_reimbursed regs _ignored s1 s2,

      ergs_reimburse_caller_and_drop (InternalCall cf caller_stack) caller_reimbursed ->
      let handler := active_exception_handler (InternalCall cf caller_stack) in

      step_xstate {|
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

        |} s1 s2 ->
      step_revert (OpRevert _ignored None) s1 s2 
        (**
 
### Case 2: `revert label` from near call, label provided

1. Pass all ergs from the current frame to the parent frame.
2. Drop current frame. 
3. Set PC to the label provided
4. Clear flags

*)
| step_RevertLocal_label:
    forall flags pages cf caller_stack caller_reimbursed regs _ignored label s1 s2,

      ergs_reimburse_caller_and_drop (InternalCall cf caller_stack) caller_reimbursed ->
      step_xstate {|
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
        |} s1 s2 ->
      
      step_revert (OpRevert _ignored (Some label)) s1 s2


(**

### Case 3: `revert abi_reg` from external call

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

All other registers are zeroed. Registers `R2`, `R3` and `R4` are reserved and may gain a special meaning in newer versions of zkEVM.
6. Context register is zeroed.
7. All storages are reverted to the state prior to the current contract call.

*)
| step_RevertExt:
  forall flags rev pages cf caller_stack xstack1 caller_reimbursed context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr fwd_mode abi_ptr_tag out_ptr cergs tx_num codes,
    let xstack0 := ExternalCall cf (Some caller_stack) in
    
    (* Panic if not a pointer *)
    resolve_load  xstack0 (regs,pages) arg (mk_pv abi_ptr_tag in_ptr_encoded) ->
    Ret.ABI.(decode) in_ptr_encoded = Some (Ret.mk_params in_ptr fwd_mode) ->

    (fwd_mode = ForwardFatPointer ->
     abi_ptr_tag &&
       negb(page_older in_ptr.(fp_page) (get_active_pages xstack0)) = true)->
    
    paid_forward fwd_mode (in_ptr, xstack0) (out_ptr, xstack1) ->
    ergs_reimburse_caller_and_drop xstack1 caller_reimbursed ->

    let encoded_out_ptr := FatPointer.ABI.(encode) out_ptr in
    step_revert (OpRevert arg label_ignored)
          {|
            gs_xstate := {|
                          gs_flags        := flags;
                          gs_callstack    := xstack0;
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
                          gs_flags        := flags_clear;
                          gs_regs         := regs_state_zero
                             <| gprs_r1 := PtrValue encoded_out_ptr |>
                             <| gprs_r2 := reg_reserved |>
                             <| gprs_r3 := reg_reserved |>
                             <| gprs_r4 := reg_reserved |> ;
                          gs_callstack    := pc_set (active_exception_handler xstack0) caller_reimbursed ;

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

## Affected parts of VM state

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


*)
