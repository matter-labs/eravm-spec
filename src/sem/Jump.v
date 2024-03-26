From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Core Common Predication GPR CallStack TransientMemory MemoryOps isa.CoreSet State
  PrimitiveValue SemanticCommon RecordSetNotations.

Section JumpDefinition.


Inductive step_jump_aux: @instruction bound -> callstack -> callstack -> Prop :=
(**

{{{
ins=Instruction(abstract_name="OpJump", mnemonic="jmp", in1=In.Any, out1=Out.Reg)
descr = InstructionDoc(
ins = ins,

syntax_override =syntax(ins) + ["`jmp in1`, alias for `jmp in1, r0`"],
summary = """
Unconditional jump (becomes conditional through predication).

**Note**: Argument `destination` uses the full addressing mode [%in_any], therefore
can be immediate 16-bit value, register, a register value with an offset, and so
on.

**Note**: in future (past VM 1.5) the output operand may gain full addressing
  mode, i.e. its type will be [%out_any].
""",

legacy = """
- `jmp destination, ret_addr`
- `jmp destination`, alias for `jmp destination, r0`
""",
semantic = """
- Fetch a new address from operand `destination`.
- Save the old PC (return address) to `return_address`. This happens after PC's
  increment, so this value equals is the addrees
- Assign to current PC the fetched value truncated to [%code_address_bits] bits.
""",

usage = """
- Unconditional jumps

- In EraVM, all instructions are predicated (see [%Predication.cond]), therefore in conjunction with a required
  condition type [%OpJump] implements a conditional jump instruction.

- Currently, the compiler may emit jumps rather than [%OpNearCall]/[%OpRet]
  and similar instructions when possible. It is cheaper, and most functions do
  not require to install a non-default [%cf_exception_handler_location], nor
  passing less than all available ergs.

- Can be used to implement cheap calling convention by playing both the role of
  call-like and ret-like instruction.

""",
similar = """
- Calls: see {CALLS}.
"""
)

describe(descr)
}}}
 *)
| step_jump_apply:
  forall (dest_val: word) (cs new_cs: callstack) tag (ret_addr: code_address) (ret_addr_w: word),

    let dest_addr := low code_address_bits dest_val in
    new_cs = pc_set dest_addr cs ->
     ret_addr = pc_get cs ->
     ret_addr_w = widen word_bits ret_addr ->
    step_jump_aux (OpJump (mk_pv tag dest_val) (IntValue ret_addr_w)) cs new_cs.

Inductive step_jump: @instruction bound -> smallstep :=
| step_Jump: forall ins (s1 s2:state),
    step_callstack (step_jump_aux ins) s1 s2 ->
    step_jump ins s1 s2.

End JumpDefinition.
