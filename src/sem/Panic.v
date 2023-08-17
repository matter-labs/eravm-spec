Require SemanticCommon VMPanic.

Import isa.CoreSet SemanticCommon VMPanic.

Inductive step_oppanic: @instruction bound -> smallstep :=
(**
# Panic (irrecoverable error, not normal return/not return from recoverable error)

Return from a function/contract signaling an error; execute exception handler,
burn all ergs in current frame, set OF flag, return nothing, perform [%rollback].
See [%Panics].

## Abstract Syntax

[%OpPanic]

## Syntax

`ret.panic` aliased as `panic` 

An abnormal return from a **near** call. Will pop up current callframe, burn
all ergs and pass control to the current exception handler, setting OF flag.

Additionally, restore storage and event queues to the state
before external call.

## Semantic

Trigger panic with a reason [%TriggeredExplicitly]. See [%Panics].

 *)
| step_trigger_panic:
  forall s s',
    step_panic TriggeredExplicitly s s' ->
    step_oppanic OpPanic s s'.

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

## Similar instructions

- `ret` returns to the caller instead of executing an exception handler, and does not burn ergs.
- `revert` acts similar to `panic` but does not burn ergs, returns data to the caller, and does not set an overflow flag.


 *)
