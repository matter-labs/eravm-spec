Require SemanticCommon.

Import Common Flags CallStack isa.CoreSet State SemanticCommon.

Section NearRetDefinition.
  Generalizable Variables __ regs pages ctx.
  Inductive step_nearret: @instruction bound -> tsmallstep :=
(** {{{!
describe(InstructionDoc(

ins=Instruction(
"Ret",
"ret",
in1 = In.Reg,
in2 = In.Reg,
out1=Out.Reg,
imm1="label",
imm2="label",
kernelOnly = False,
notStatic = False),

syntax_override = [],
legacy = "`ret.ok` aliased as `ret`",

preamble= r"""
This instruction is used to return from both far and near calls.

- if the topmost frame in callstack is [%ExternalCall], the FarRet semantic is
  selected (see [%FarRetDefinition]);
- if the topmost frame in callstack is [%InternalCall], the NearRet semantic is
  selected (see [%NearRetDefinition]).
""",
summary = """
A normal return from a **near** call. Will pop up current callframe, give back unspent ergs and
continue execution from the saved return address (from where the call had taken place).
""",

semantic = r"""
1. Pass all ergs from the current frame to the parent frame.
2. Drop current frame.
3. Clear flags.
""",
affectedState = """
- Execution stack:
  + Current frame is dropped.
  + Caller frame:
    * Unspent ergs are given back to caller (but memory growth is paid first).

- Flags are cleared.
""",
usage = "Normal return from functions.",
similar = f"See {RETS}."
))
}}} *)
  | step_NearRet:
    forall cf caller_stack new_caller pages _ignore_arg,
      `(
          ergs_return_caller_and_drop (InternalCall cf caller_stack) new_caller ->

          step_nearret (OpRet _ignore_arg) {|
                         gs_flags        := __;
                         gs_callstack    := InternalCall cf caller_stack;


                         gs_regs         := regs;
                         gs_pages        := pages;
                         gs_context_u128 := ctx;
                         gs_status       := NoPanic;
                       |}
                       {|
                         gs_flags        := flags_clear;
                         gs_callstack    := new_caller;


                         gs_regs         := regs;
                         gs_pages        := pages;
                         gs_context_u128 := ctx;
                         gs_status       := NoPanic;
                       |}
        )
  .

  Generalizable No Variables.
End NearRetDefinition.
