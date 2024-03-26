Require SemanticCommon.

Import Common Flags CallStack GPR TransientMemory isa.CoreSet State SemanticCommon.

Section NearRevert.
  Generalizable Variables regs pages __.
  Inductive step_nearrevertto: @instruction bound -> smallstep :=
(** {{{!
describe(InstructionDoc(
ins=Instruction("OpNearRevertTo", "revl", imm1="label"),

legacy = """`ret.revert label` aliased as `revert label`""",

summary = """
An erroneous return from a **near** call to a specified label. Will revert all
changes in [%global_state] produced in the current frame, pop up current
frame, give back unspent ergs, and proceed to execute exception handler.

The assembler expands `revert label` to `revert r1, label`, but `r1` is
ignored by returns from near calls.
""",

semantic = r"""
1. Perform a [%rollback].
2. Pass all ergs from the topmost frame to the parent frame.
3. Drop topmost frame.
4. Clear flags
5. Proceed with executing [%label], i.e. replace program counter with the label's value.
""",
affectedState = """
- Flags are cleared.
- Execution stack:
  + Current frame is dropped.
  + Caller frame:
    * Unspent ergs are given back to caller (but memory growth is paid first).
    * Program counter is overwritten with the label.
""",
usage = """ Return from a recoverable error, fail-safe. """,
similar = f"""See {RETS}"""
))
}}}
   *)
  | step_NearRevert:
    forall cf caller_stack new_caller _eh _sp _pc _ergs saved ctx label gs new_gs pages,
      `(
          let cs := InternalCall (mk_cf _eh _sp _pc _ergs saved) caller_stack in
          let handler := active_exception_handler cs in

          ergs_return_caller_and_drop cs new_caller ->
          rollback saved gs new_gs ->
          step_nearrevertto (OpNearRevertTo label)
                            {|
                              gs_transient := {|
                                               gs_flags        := __ ;
                                               gs_callstack    := InternalCall cf caller_stack;

                                               gs_regs         := regs;
                                               gs_pages        := pages;
                                               gs_context_u128 := ctx;
                                               gs_status       := NoPanic;
                                             |};
                              gs_global := gs;
                            |}
                            {|
                              gs_transient := {|
                                               gs_flags        := flags_clear;
                                               gs_callstack    := pc_set label new_caller;

                                               gs_regs         := regs;
                                               gs_pages        := pages;
                                               gs_context_u128 := ctx;
                                               gs_status       := NoPanic;
                                             |};
                              gs_global := new_gs;
                            |}
        )
  .
End NearRevert.
