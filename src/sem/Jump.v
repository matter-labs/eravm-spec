From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Common Condition ExecutionStack Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations.

Section Def.
  
Context (regs: regs_state) (old_pages:pages) (xstack: execution_stack).
Let resolve := resolve_fetch_value regs xstack old_pages.

Inductive step_jump: instruction -> execution_stack -> Prop :=
(**

## `jump`

Unconditional jump.

### Abstract Syntax

[ OpJump (dest: in_any)]

### Syntax

- `jump label`

Note: Argument `label` uses the full addressing mode, therefore can be immediate
16-bit value, register, a register value with an offset, and so on.

### Semantic

- Fetch a new address from operand `label`.

- Assign to current PC the fetched value truncated to [code_address_bits] bits.
 *)
| step_jump_apply:
  forall (dest:in_any) (dest_val: word) (any_tag: bool)
    (new_xstack: execution_stack),
    
    resolve dest (mk_pv any_tag dest_val) ->
      
    let dest_addr := resize _ code_address_bits dest_val in
    new_xstack = pc_set dest_addr xstack ->
    
    step_jump (OpJump dest) new_xstack.

(**

### Affected parts of VM state

- execution stack: PC is overwritten with a new value.

### Usage

- Unconditional jumps

- In zkEVM, all instructions are predicated (see [Condition.cond]), therefore in conjunction with a required
  condition type [jump] implements a conditional jump instruction.

### Similar instructions

- Calls: see [OpNearCall], [OpFarCall], [OpDelegateCall], [OpMimicCall].

*)

End Def.

Inductive step: instruction -> smallstep :=
| step_Jump: forall regs pages xstack new_xstack flags context_u128 gs ins,
  step_jump regs pages xstack ins new_xstack->
  step ins
        {|
          gs_callstack    := xstack;


          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          gs_context_u128 := context_u128;
          gs_global       := gs;
        |}
        {|
          gs_callstack    := new_xstack;


          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          gs_context_u128 := context_u128;
          gs_global       := gs;
        |}
.
