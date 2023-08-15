From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Core Common Predication GPR CallStack Memory MemoryOps isa.CoreSet State ZMod
  PrimitiveValue SemanticCommon RecordSetNotations.

Section Def.


Inductive step_jump_aux: @instruction bound -> callstack -> callstack -> Prop :=
(**

## `jump`

Unconditional jump.

### Abstract Syntax

[% OpJump (dest: in_any)]

### Syntax

- `jump destination`

Note: Argument `destination` uses the full addressing mode [%in_any], therefore can be immediate
16-bit value, register, a register value with an offset, and so on.

### Semantic

- Fetch a new address from operand `destination`.

- Assign to current PC the fetched value truncated to [%code_address_bits] bits.
 *)
| step_jump_apply:
  forall (dest_val: word) (cs new_cs: callstack) __,

    let dest_addr := resize _ code_address_bits dest_val in
    new_cs = pc_set dest_addr cs ->

    step_jump_aux (OpJump (mk_pv __ dest_val)) cs new_cs.

(**

### Affected parts of VM state

- execution stack: PC is overwritten with a new value.

### Usage

- Unconditional jumps

- In EraVM, all instructions are predicated (see [%Predication.cond]), therefore in conjunction with a required
  condition type [%jump] implements a conditional jump instruction.

- Currently, the compiler may emit jumps rather than [%OpNearCall]/[%OpNearRet]
  and similar instructions when possible. It is cheaper, and most functions do
  not require to install a non-default [%cf_exception_handler_location], nor
  passing less than all available ergs.

### Similar instructions

- Calls: see [%OpNearCall], [%OpFarCall], [%OpDelegateCall], [%OpMimicCall].

*)

End Def.

Inductive step_jump: @instruction bound -> smallstep :=
| step_Jump: forall ins (s1 s2:state),
    step_callstack (step_jump_aux ins) s1 s2 ->
    step_jump ins s1 s2.
