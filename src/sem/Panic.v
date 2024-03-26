Require SemanticCommon VMPanic StepPanic.

Import isa.CoreSet SemanticCommon VMPanic StepPanic.

Inductive step_oppanic: @instruction bound -> smallstep :=
  (** {{{!
describe(InstructionDoc(
ins=Instruction(
"OpPanic",
"panic",
kernelOnly = False,
notStatic = False),
add_to_title = "(irrecoverable error, not normal return/not return from recoverable error)",
legacy = " `ret.panic` aliased as `panic`",
preamble = None,

summary = """
Return from a function/contract signaling an error; execute exception handler,
return unspent ergs to the parent, set OF flag, return nothing, perform
[%rollback].
""",

semantic = r"""
An abnormal return from a **near** call. Will drop current callframe, burn
all ergs and pass control to the current exception handler, setting OF flag.

Additionally, restore storage, transient storage, and event queues to the state
before external call.
""",
affectedState = r"""
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
""",
usage = """
- Abnormal returns from near/far calls when an irrecoverable error has happened.
  Use [%OpRevert] for recoverable errors.
""",
similar = f"See {RETS}."
))
}}}
*)

| step_trigger_panic:
  forall s s',
    step_panic TriggeredExplicitly s s' ->
    step_oppanic OpPanic s s'.

