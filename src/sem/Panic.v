Require SemanticCommon VMPanic.

Import isa.CoreSet SemanticCommon VMPanic.

Inductive step_oppanic: @instruction bound -> smallstep :=
(**
## Panic (irrecoverable error, not normal return/not return from recoverable error)

Return from a function signaling an error; execute exception handler, burn all
ergs in current frame, set OF flag, return no data.

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

1. Perform a [%rollback].
2. Drop current frame with its ergs.
3. Set PC to the exception handler of a dropped frame.
4. Clear flags, and set OF.
 *)
| step_trigger_panic:
  forall s s',
    step_panic TriggeredExplicitly s s' ->
    step_oppanic OpPanic s s'.

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
