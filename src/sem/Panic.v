From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Common Condition CallStack Memory MemoryOps Instruction State ZMod
  ABI ABI.Ret ABI.FatPointer Addressing.Coercions SemanticCommon RecordSetNotations.
        


Inductive step_panic: instruction -> smallstep :=
(**

# `panic` (irrecoverable error, not normal return/not return from recoverable error)

Return from a function signaling an error; execute exception handler, burn all
regs in current frame, set OF flag, return no data.

## Abstract Syntax

- [OpPanic (args: in_reg) (label: option code_address)]

## Syntax

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
  

## Semantic

### Common notes

- `panic` always clears flags and sets OF.
- panics from far calls ignore an explicit label from the instruction.
- panic can't pass data to caller.
- most errors in executing of other instructions lead to executing `panic` instead.


### Case 1: `panic` from near call, no label

1. Drop current frame with its ergs.
2. Set PC to the exception handler of a dropped frame.
3. Clear flags, and set OF.

 *)


| step_PanicLocal_nolabel:
    forall s1 s2 flags pages cf caller_stack regs,

      (* no reimbursement, ergs are lost *)
      let handler := active_exception_handler (InternalCall cf caller_stack) in
      
      step_xstate {|
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
          |} s1 s2 ->
      
      step_panic (OpPanic None) s1 s2
                 
        (**

### Case 2: `panic` from near call, label provided

1. Drop current frame with its ergs.
2. Set PC to label value.
3. Clear flags, and set OF.

 *)
| step_PanicLocal_label:
    forall flags pages cf caller_stack regs _ignored label s1 s2,

      step_xstate
        {|
          gs_flags        := flags;
          gs_callstack    := InternalCall cf caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
        |}
        {|
          gs_flags        := set_overflow flags_clear;
          gs_callstack    := pc_set label caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
        |}
        s1 s2 ->
        step_panic (OpRet _ignored (Some label)) s1 s2
(**

### Case 3: `revert` from external call

1. Drop current frame and its ergs
2. Clear flags and set OF.
3. Clear context register.
4. Set PC to the exception handler address of a dropped frame.
5. All storages are reverted to the state prior to the current contract call.
6. Context register is zeroed.
7. Put an encoded zero-pointer into `R1` and tag `R1` as a pointer.

   All other registers are zeroed. Registers `R2`, `R3` and `R4` are reserved
   and may gain a special meaning in newer versions of zkEVM.

*)
| step_PanicExt:
  forall codes flags rev pages cf caller_stack context_u128 regs label_ignored (arg:in_reg) cergs tx_num,
    let xstack0 := ExternalCall cf (Some caller_stack) in

    let encoded_out_ptr := FatPointer.ABI.(encode) fat_ptr_empty in
    step_panic (OpPanic label_ignored)
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
                          gs_flags        := set_overflow flags_clear;
                          gs_regs         := regs_state_zero
                             <| gprs_r1 := PtrValue encoded_out_ptr |>
                             <| gprs_r2 := reg_reserved |>
                             <| gprs_r3 := reg_reserved |>
                             <| gprs_r4 := reg_reserved |> ;
                          gs_callstack    := pc_set (active_exception_handler xstack0) caller_stack;

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
 
## Usage

- Abnormal returns from near/far calls when an irrecoverable error has happened.
Use `revert` for recoverable errors.
- An attempt of executing an invalid instruction will result in executing `panic`.
- Most error situations happening during execution will result in executing `panic`.

## Similar instructions

- `ret` returns to the caller instead of executing an exception handler, and does not burn ergs.
- `revert` acts similar to `panic` but does not burn ergs and lets pass any data to the caller, and does not set an overflow flag.


*)
