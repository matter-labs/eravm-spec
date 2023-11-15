From RecordUpdate Require Import RecordSet.
Require SemanticCommon StepPanic.

Import Common Flags CallStack GPR TransientMemory isa.CoreSet State SemanticCommon VMPanic RecordSetNotations StepPanic isa.CoreSet.

Section NearPanicToDefinition.
Inductive step_panicto: instruction -> smallstep :=
(** # NearPanic (abnormal return, not return/revert)

## Abstract Syntax

[%OpNearPanicTo]

## Syntax

`ret.panic label` aliased as `panic label`

  An erroneous return from a **near** call to a specified label. Will revert all
  changes in [%global_state] produced in the current frame, drop the current
  frame, give back unspent ergs, and proceed to execute exception handler.

  The assembler expands `panic label` to `panic r1, label`, but `r1` is
  ignored by returns from near calls.

## Semantic

1. Perform a [%rollback].
2. Drop topmost frame. Its ergs are burned (lost).
3. Set flag [%OF_LT], clear all other flags.
4. Proceed with executing [%label], i.e. replace program counter with the label's value.
 *)
| step_NearPanic:
    forall label s1 s2 s3,
      step_panic TriggeredExplicitly s1 s2 ->
      s3 = s2 <| gs_transient ::= fun ts => ts <| gs_callstack ::= pc_set label  |> |> ->
      step_panicto (@OpNearPanicTo bound label) s1 s3
.
(** ## Affected parts of VM state

- Flags are cleared.
- Execution stack:
  + Current frame is dropped.
  + Caller frame:
    * Unspent ergs are given back to caller (but memory growth is paid first).
    * Program counter is overwritten with the exception handler address of the dead frame.

## Usage

Return from an irrecoverable error, fail-fast.
 *)
End NearPanicToDefinition.
