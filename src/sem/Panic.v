From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Coder Common Flags CallStack GPR Memory MemoryOps Instruction State ZMod
  ABI FatPointer Addressing.Coercions Pointer PrimitiveValue SemanticCommon RecordSetNotations.

Inductive step_panic: instruction -> xsmallstep :=
(**
## Panic (irrecoverable error, not normal return/not return from recoverable error)

Return from a function signaling an error; execute exception handler, burn all
regs in current frame, set OF flag, return no data.

### Abstract Syntax

[%OpPanic]

### Syntax

- `panic` (when topmost frame is [%InternalCall])

  An abnormal return from a **near** call. Will pop up current callframe, burn all ergs and
  pass control to the current exception handler, setting OF flag.

- `panic` (when topmost frame is [%ExternalCall])

  An abnormal return from a **far** call. Will pop up current callframe, burn all ergs and
  execute a current exception handler, setting OF flag.

  Restores storage to the state before external call.


### Semantic

#### Common notes

- `panic` always clears flags and sets OF.
- panics from far calls ignore an explicit label from the instruction.
- panic can't pass data to caller.
- most errors in executing of other instructions lead to executing `panic` instead.


#### Case 1: `panic` from near call

1. Perform a [%roll_back].
2. Drop current frame with its ergs.
3. Set PC to the exception handler of a dropped frame.
4. Clear flags, and set OF.
*)


| step_PanicLocal_nolabel:
    forall flags pages cf caller_stack regs gs gs' __,

      (* no reimbursement, ergs are lost *)
      let handler := active_exception_handler (InternalCall cf caller_stack) in

      roll_back (cf_saved_checkpoint cf) gs gs' ->
      step_panic OpPanic
                 {|
            gs_xstate := {|
                          gs_flags        := flags;
                          gs_callstack    := InternalCall cf caller_stack;

                          gs_regs         := regs;


                          gs_pages        := pages;
                        |};
            gs_context_u128 := __;

            gs_global       := gs;
          |}
          {|
            gs_xstate := {|
                          gs_flags        := set_overflow flags_clear;
                          gs_regs         := regs_state_zero;
                          gs_callstack    := pc_set cf.(cf_exception_handler_location) caller_stack;

                          gs_pages        := pages;
                          |};


          gs_context_u128 := zero128;

          gs_global       := gs'
          |}

(**

#### Case 2: `panic` from external call

1. Perform a [%roll_back].
2. Drop current frame and its ergs
3. Clear flags and set OF.
4. Clear context register.
5. Set PC to the exception handler address of a dropped frame.
6. All storages are reverted to the state prior to the current contract call.
7. Put an encoded zero-pointer into `R1` and tag `R1` as a pointer.

   All other registers are zeroed. Registers `R2`, `R3` and `R4` are reserved
   and may gain a special meaning in newer versions of EraVM.
*)
| step_PanicExt:
  forall flags pages cf caller_stack __ regs (arg:in_reg) gs gs',
    let cs0 := ExternalCall cf (Some caller_stack) in
    roll_back (cf_saved_checkpoint cf) gs gs' ->
    step_panic OpPanic
          {|
            gs_xstate := {|
                          gs_flags        := flags;
                          gs_callstack    := cs0;
                          gs_regs         := regs;


                          gs_pages        := pages;
                        |};
            gs_context_u128 := __;

            gs_global       := gs;
          |}
          {|
            gs_xstate := {|
                          gs_flags        := set_overflow flags_clear;
                          gs_regs         := regs_state_zero;
                          gs_callstack    := pc_set (active_exception_handler cs0) caller_stack;

                          gs_pages        := pages;
                          |};


          gs_context_u128 := zero128;

          gs_global       := gs'
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
