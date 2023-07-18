Require SemanticCommon.

Import Common Flags CallStack GPR Memory Instruction State SemanticCommon.

Section NearRet.
Generalizable Variables regs flags pages s.
Inductive step_ret: instruction -> xsmallstep :=
(**

# NearRet (normal return, not panic/revert)

## Abstract Syntax

[%OpNearRet]

## Syntax

`ret.ok` aliased as `ret`

  A normal return from a **near** call. Will pop up current callframe, give back unspent ergs and
  continue execution from the saved return address (from where the call had taken place).

  The assembler expands `ret` to `ret r1`, but `r1` is ignored by returns from near calls.

## Semantic


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
.
(**

## Affected parts of VM state

- Flags are cleared.
- Execution stack:
  + Current frame is dropped.
  + Caller frame:
    * Unspent ergs are given back to caller (but memory growth is paid first).

## Usage

Normal return from functions.
*)
End NearRet.
