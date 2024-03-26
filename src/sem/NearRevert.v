Require SemanticCommon.

Import Common Flags CallStack GPR TransientMemory isa.CoreSet State SemanticCommon.

Section NearRevertDefinition.
  Generalizable Variables regs __.

  Inductive step_nearrevert: @instruction bound -> smallstep :=
(** {{{!
describe(InstructionDoc(
ins=Instruction(
"OpNearRevert",
"rev",
in1 = In.Reg,
),
add_to_title = "(case of near revert)",
legacy = "`ret.revert` aliased as `revert`",
preamble = r"""
The NearRevert and FarRevert share the same syntax, but their runtime semantic is
different:

- if the topmost frame in callstack is [%ExternalCall], the FarRet semantic is
  selected (see [%FarRetDefinition]);
- if the topmost frame in callstack is [%InternalCall], the NearRet semantic is
  selected (see [%NearRetDefinition]).
""",

summary = """
An erroneous return from a **near** call, executes an exception handler. Will
revert all changes in [%global_state] produced in the current frame, pop up
current frame, give back unspent ergs, and proceed to execute exception
handler.

The assembler expands `revert` to `revert r1`, but `r1` is ignored by returns
from near calls.
""",

semantic = r"""
1. Perform a [%rollback].
2. Retrieve an exception handler $E$ from the current frame.
3. Pass all ergs from the topmost frame to the parent frame.
4. Drop topmost frame.
5. Clear flags
6. Proceed with executing $E$.
""",
affectedState = """
- Flags are cleared.
- Execution stack:
  + Current frame is dropped.
  + Caller frame:
    * Unspent ergs are given back to caller (but memory growth is paid first).
    * Program counter is overwritten with the exception handler address of the dead frame.
""",
usage = """ Return from a recoverable error, fail-safe. """,
similar = f"See {RETS}."
))
}}}
*)
  | step_NearRevert:
    forall cf caller_stack new_caller new_cs _eh _sp _pc _ergs saved ctx gs new_gs pages _ignore_arg,
      `(
          let cs := InternalCall (mk_cf _eh _sp _pc _ergs saved) caller_stack in
          let handler := active_exception_handler cs in

          ergs_return_caller_and_drop cs new_caller ->
          rollback saved gs new_gs ->
          new_cs = pc_set handler new_caller ->
          step_nearrevert (OpRevert _ignore_arg)
                          {|
                            gs_transient := {|
                                             gs_flags        := __;
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
                                             gs_callstack    := new_cs;

                                             gs_regs         := regs;
                                             gs_pages        := pages;
                                             gs_context_u128 := ctx;
                                             gs_status       := NoPanic;
                                           |};
                            gs_global := new_gs;
                          |}
        )
  .


  Generalizable No Variables.
End NearRevertDefinition.
