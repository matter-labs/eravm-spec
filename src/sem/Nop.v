Require SemanticCommon.

Import Core isa.CoreSet State SemanticCommon.

Section NoOpDefinition.
(** {{{!
describe(InstructionDoc(

ins=Instruction(abstract_name = "OpNoOp", mnemonic = "nop"),
summary = """
Do nothing.
""",

semantic = r"""
Do nothing.
""",

similar = """
 - [%OpNoOp], [%OpSpAdd], [%OpSpSub] are encoded as the same instruction.
""",
usage = ""
))
}}}
   *)
  Inductive step_nop: @instruction bound -> smallstep :=
  | step_NoOp:
    forall s, step_nop OpNoOp s s
  .

End NoOpDefinition.
