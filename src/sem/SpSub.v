Require SemanticCommon.

Import Arith Addressing CallStack Core isa.CoreSet TransientMemory Resolution State SemanticCommon PrimitiveValue spec.

Section SpSubDefinition.

  Open Scope ZMod_scope.
  (**{{{!
describe(InstructionDoc(

ins=Instruction(abstract_name = "OpSpSub", mnemonic = "decsp", in1 = In.Reg, in2 = In.Imm),

syntax_override = ["`decsp reg+imm`", "`decsp reg`", "`decsp imm`"],

legacy = r"`nop stack-=[reg+imm]`",
summary = " Subtract `(reg + imm)` from SP.",

semantic = r"""
$\mathit{SP_{new} := SP - (reg + imm)}$, but only if there was no overflow.
""",

usage = """
- Adjusting SP e.g. deallocating space on stack.
""",

similar = """
- [%OpSpAdd] increases SP.
- [%OpNoOp], [%OpSpAdd] and [%OpSpSub] are encoded as the same instruction.
"""
))
}}}
 *)
  Inductive step_sp_sub : instruction -> callstack_smallstep :=
  | step_op_sp_sub:
    forall (cs0 new_cs: callstack) (old_sp intermediate_sp new_sp ofs: stack_address) op __,
      sp_get cs0 = old_sp ->
      (false, intermediate_sp) = old_sp + (low stack_address_bits op) ->
      (false, new_sp) = intermediate_sp - ofs->
      new_cs = sp_update new_sp cs0 ->
      step_sp_sub (OpSpSub (mk_pv __ op) ofs) cs0 new_cs
  .

End SpSubDefinition.
