Require SemanticCommon.

Import Arith Addressing CallStack Core isa.CoreSet TransientMemory Resolution State SemanticCommon PrimitiveValue spec.

Section SpAddDefinition.

  Open Scope ZMod_scope.
  Inductive step_sp_add : instruction -> callstack_smallstep :=
(**{{{!
describe(InstructionDoc(

ins=Instruction(abstract_name = "OpSpAdd", mnemonic = "incsp", in1 = In.Reg, in2 = In.Imm),

syntax_override = ["`incsp reg+imm`", "`incsp reg`", "`incsp imm`"],

legacy = r"`nop r0, r0, stack+=[reg+imm]`",
summary = " Add `(reg + imm)` to SP.",

semantic = r"""
$\mathit{SP_{new} := SP + (reg + imm)}$, but only if there was no overflow.
""",

usage = """
- Adjusting SP e.g. reserving space on stack.
""",

similar = """
- [%OpSpSub] subtracts a value from SP.
- [%OpNoOp], [%OpSpAdd] and [%OpSpSub] are encoded as the same instruction.
"""
))
}}}
 *)
  | step_op_sp_add:
    forall (cs0 new_cs: callstack) (old_sp intermediate_sp new_sp ofs: stack_address) op __,
      sp_get cs0 = old_sp ->
      (false, intermediate_sp) = old_sp + (low stack_address_bits op) ->
      (false, new_sp) = intermediate_sp + ofs->
      new_cs = sp_update new_sp cs0 ->
      step_sp_add (OpSpAdd (mk_pv __ op) ofs) cs0 new_cs
  .

End SpAddDefinition.
