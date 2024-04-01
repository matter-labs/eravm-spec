Require SemanticCommon.

Import Common Flags CallStack isa.CoreSet State SemanticCommon.

Section NearRetToDefinition.
  Generalizable Variables __ regs pages ctx.
  Inductive step_nearretto: @instruction bound -> tsmallstep :=
(** {{{!
describe(InstructionDoc(

ins = Instruction("OpNearRetTo", "retl", imm1="label"),
legacy = "`ret.ok.to_label label` ",
summary = """
A normal return from a **near** call. Will pop up current callframe, give back
unspent ergs and continue execution from an explicitly provided label.
""",

semantic = r"""
1. Pass all ergs from the current frame to the parent frame.
2. Drop current frame.
3. Clear flags
4. Set PC to the label value.
""",
affectedState = """
- Flags are cleared.
- Execution stack:
  + Current frame is dropped.
  + Caller frame:
    * Unspent ergs are given back to caller (but memory growth is paid first).
    * program counter is assigned the label.
""",
usage = "A combination of a normal return and jump.",
similar = f"See {RETS}."
))
}}} *)

  | step_NearRetTo:
    forall cf caller_stack new_caller label,
      `(
          ergs_return_caller_and_drop (InternalCall cf caller_stack) new_caller ->

          step_nearretto (OpNearRetTo label) {|
                           gs_flags        := __;
                           gs_callstack    := InternalCall cf caller_stack;


                           gs_regs         := regs;
                           gs_pages        := pages;
                           gs_context_u128 := ctx;
                           gs_status       := NoPanic;
                         |}
                         {|
                           gs_flags        := flags_clear;
                           gs_callstack    := pc_set label new_caller;


                           gs_regs         := regs;
                           gs_pages        := pages;
                           gs_context_u128 := ctx;
                           gs_status       := NoPanic;
                         |}
        )
  .
  Generalizable No Variables.
End NearRetToDefinition.
