From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Common Condition ExecutionStack Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations.

Inductive step: instruction -> smallstep :=
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
| step_Jump:
    forall gs flags pages xstack context_u128 regs (dest:in_any) dest_val any_tag,
      resolve_fetch_value regs xstack pages dest (mk_pv any_tag dest_val) ->
      let dest_addr := resize _ code_address_bits dest_val in
      step (OpJump dest)
        {|
          gs_callstack    := xstack;


          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          gs_context_u128 := context_u128;
          gs_global       := gs;
        |}
        {|
          gs_callstack    := pc_set dest_addr xstack;


          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          gs_context_u128 := context_u128;
          gs_global       := gs;
        |}
.

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


