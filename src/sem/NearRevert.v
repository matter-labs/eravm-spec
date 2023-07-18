Require SemanticCommon.

Import Common Flags CallStack GPR Memory Instruction State SemanticCommon.

Section NearRevert.
Generalizable Variables regs flags pages s __.
Inductive step_revert: instruction -> xsmallstep :=
(**

# NearRevert (return with recoverable error)

## Abstract Syntax

[%OpNearRevert]

## Syntax

`ret.revert` aliased as `revert`

  An erroneous return from a **near** call to a specified label. Will revert all
  changes in [%global_state] produced in the current frame, pop up current
  frame, give back unspent ergs, and proceed to execute exception handler.

  The assembler expands `revert` to `revert r1`, but `r1` is ignored by returns
  from near calls.

## Semantic

1. Perform a [%roll_back].
2. Retrieve an exception handler $E$ from the current frame.
3. Pass all ergs from the topmost frame to the parent frame.
4. Drop topmost frame.
5. Clear flags
6. Proceed with executing $E$.
 *)
| step_NearRevert:
    forall cf caller_stack caller_reimbursed _eh _sp _pc _ergs saved ctx gs new_gs,
      `(
          let cs := InternalCall (mk_cf _eh _sp _pc _ergs saved) caller_stack in
          let handler := active_exception_handler cs in

          ergs_reimburse_caller_and_drop cs caller_reimbursed ->
          roll_back saved gs new_gs ->
          step_revert OpNearRevert
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
                                      gs_flags        := flags_clear;
                                      gs_callstack    := pc_set handler caller_reimbursed;

                                      gs_regs         := regs;
                                      gs_pages        := pages;
                                    |};
                        gs_context_u128 := ctx;
                        gs_global := new_gs;
                      |}
        )
.
(**

## Affected parts of VM state

- Flags are cleared.
- Execution stack:
  + Current frame is dropped.
  + Caller frame:
    * Unspent ergs are given back to caller (but memory growth is paid first).
    * Program counter is overwritten with the exception handler address of the dead frame.

## Usage

Return from a recoverable error, fail-safe.
 *)
End NearRevert.
