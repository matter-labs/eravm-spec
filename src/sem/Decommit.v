From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Core Common Predication GPR CallStack TransientMemory MemoryOps isa.CoreSet State
  PrimitiveValue SemanticCommon RecordSetNotations.

Section DecommitDefinition.


  Inductive step_decommit: @instruction decoded -> smallstep :=
(** {{{!
describe(InstructionDoc(

ins=Instruction("OpDecommit", "dcmt", in1 = In.Reg, in2 = In.Reg, out1=Out.Reg, kernelOnly = True ),
legacy = " `decommit in1, in2, out1`",
summary = " Decommit code into memory.",

semantic = r"""
FIXME
""",

usage = """
- Read data from a read-only slice returned from a far call, or passed to a far call.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc].
"""
))
}}}
 *)
    (* FIXME: no semantic yet *)
| step_decommit_apply:
  forall src0 src1 dst0 (s: state),

    step_decommit (OpDecommit src0 src1 dst0) s s.

End DecommitDefinition.
