From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Core Common Predication GPR CallStack TransientMemory MemoryOps isa.CoreSet State
  PrimitiveValue SemanticCommon RecordSetNotations.

Section JumpDefinition.


Inductive step_jump_aux: @instruction bound -> callstack -> callstack -> Prop :=
(** # Jump

Unconditional jump (becomes conditional through predication).

## Abstract Syntax

[% OpJump (dest: in_any) (return_address: out_reg)]

Note: in future (past VM 1.5) the output operand may gain full addressing mode, i.e. its type will be [%out_any].

# Syntax

- `jmp destination, ret_addr`
- `jmp destination`, alias for `jmp destination, r0`


## Legacy Syntax

- `jump destination`

Note: Argument `destination` uses the full addressing mode [%in_any], therefore can be immediate
16-bit value, register, a register value with an offset, and so on.

## Semantic

- Fetch a new address from operand `destination`.
- Save the old PC (return address) to `return_address`
- Assign to current PC the fetched value truncated to [%code_address_bits] bits.

FIXME semantic is obsolete
 *)
| step_jump_apply:
  forall (dest_val: word) (cs new_cs: callstack) tag1 tag2 ret_addr,

    let dest_addr := low code_address_bits dest_val in
    new_cs = pc_set dest_addr cs ->

    step_jump_aux (OpJump (mk_pv tag1 dest_val) (mk_pv tag2 ret_addr)) cs new_cs.

(** ## Affected parts of VM state

- execution stack: PC is overwritten with a new value.

## Usage

- Unconditional jumps

- In EraVM, all instructions are predicated (see [%Predication.cond]), therefore in conjunction with a required
  condition type [%jump] implements a conditional jump instruction.

- Currently, the compiler may emit jumps rather than [%OpNearCall]/[%OpNearRet]
  and similar instructions when possible. It is cheaper, and most functions do
  not require to install a non-default [%cf_exception_handler_location], nor
  passing less than all available ergs.

- Can be used to implement cheap calling convention by playing both the role of
  call-like and ret-like instruction.

## Similar instructions

- Calls: see [%OpNearCall], [%OpFarCall], [%OpDelegateCall], [%OpMimicCall].

*)

Inductive step_jump: @instruction bound -> smallstep :=
| step_Jump: forall ins (s1 s2:state),
    step_callstack (step_jump_aux ins) s1 s2 ->
    step_jump ins s1 s2.

End JumpDefinition.
