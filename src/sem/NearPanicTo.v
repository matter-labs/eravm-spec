Require SemanticCommon.

Import Common Flags CallStack GPR Memory Instruction State SemanticCommon.

Section NearPanic.
Generalizable Variables regs flags pages gs s __.
Inductive step_panic: forall descr, @instruction descr -> smallstep :=
(**

# NearPanic (abnormal return, not return/panic)

## Abstract Syntax

[%OpNearPanicTo]

## Syntax

`ret.panic label` aliased as `panic label`

  An erroneous return from a **near** call to a specified label. Will panic all
  changes in [%global_state] produced in the current frame, pop up current
  frame, give back unspent ergs, and proceed to execute exception handler.

  The assembler expands `panic label` to `panic r1, label`, but `r1` is
  ignored by returns from near calls.

## Semantic

1. Perform a [%roll_back].
2. Drop topmost frame. Its ergs are burned (lost).
3. Set flag [%OF_LT], clear all other flags.
4. Proceed with executing [%label], i.e. replace program counter with the label's value.
 *)
| step_NearPanic:
    forall cf caller_stack caller_reimbursed _eh _sp _pc _ergs saved ctx label descr,
      `(
          let cs := InternalCall (mk_cf _eh _sp _pc _ergs saved) caller_stack in
          let handler := active_exception_handler cs in

          roll_back saved gs gs' ->
          step_panic descr (OpNearPanicTo label)
                      {|
                        gs_xstate := {|
                                       gs_flags        := flags;
                                       gs_callstack    := InternalCall cf caller_stack;

                                       gs_regs         := regs;
                                       gs_pages        := pages;
                                     |};
                        gs_context_u128 := ctx;
                        gs_global := gs;
                      |}
                      {|
                        gs_xstate := {|
                                      gs_flags        := set_overflow flags_clear;
                                      gs_callstack    := pc_set label caller_reimbursed;

                                      gs_regs         := regs;
                                      gs_pages        := pages;
                                    |};
                        gs_context_u128 := ctx;
                        gs_global := gs';
                      |}
        )
.
(** ## Affected parts of VM state

- Flags are cleared.
- Execution stack:
  + Current frame is dropped.
  + Caller frame:
    * Unspent ergs are given back to caller (but memory growth is paid first).
    * Program counter is overwritten with the exception handler address of the dead frame.

## Usage

Return from a recoverable error, fail-safe.
 *)
End NearPanic.
