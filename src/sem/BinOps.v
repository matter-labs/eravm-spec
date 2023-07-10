Require sem.SemanticCommon.

Import Addressing Bool ZArith Common Flags Instruction CallStack Memory MemoryOps State ZMod
  ZBits Addressing.Coercions PrimitiveValue SemanticCommon.
(**
#  Common binary operation semantic

The predicate [binop_effect_spec] describes a scheme of execution shared by binary operations:

- `add`
- `sub`
- `and`
- `or`
- `xor`
- `ror`
- `rol`
- `shr`
- `shl`

All these instructions follow the abstract syntax template:

`<OPCODE> (in1: in_any) (in2:in_reg) (out: out_any) (swap_mod:bool) (set_flags_mod:bool)`


The operation follows a similar scheme as described below.

1. **Resolve and fetch `op1` from `in1`** ::  Fetch operand `op1` from `in1`. It uses full addressing mode, i.e. can be taken from registers, memory, in absolute or relative way.
2. **Adjust SP** :: If `in1` affects SP through an addressing mode `RelSpPop`, SP is decremented by a specified value.
3. **Fetch `op2` from `in2`** :: Fetch operand `op2` from `in2`. It can only use registers, therefore does not affect SP.
4. **Resolve `out`** :: Resolve location of `out`. It uses a full addressing mode, therefore the destination can be register, stack, it can be addressed relatively to GPR and so on.
5. **Adjust SP again** :: If `out` affects SP through an addressing mode `RelSpPush`, SP is adjusted.
6. **Account for `swap`** :: If `swap` modifier is set, operands are swapped, i.e. `op1` becomes `op2`, and `op2` becomes `op1`. This allows e.g. subtracting a stack memory value from register: `sub.s r1, stack[1], r3`
7. **Perform operation-specific computations** :: Add operands, subtract them, perform bitwise operations, and so on. Additionally, compute a `flags_candidate` value depending on the operation result.
8. **Commit or discard new flags** :: If `set_flags` modifier is set, flags are set according to `flags_candidate`; otherwise all flags are preserved and `flags_candidate` is discarded.
9. **Store result**:: Write `result` to a location resolved on step 4.


Note that predicate [binop_effect_spec] is a relation that binds `in1`, `in2`, `out`, `op1`, `op2`, `result`, `flags_candidate`; the computations specific to the operation will be described in specific constructors like [step_Add].
 *)

Inductive binop_effect_spec:
                        mod_swap -> mod_set_flags ->
                        in_any * primitive_value ->
                        in_reg * primitive_value ->
                        out_any* primitive_value ->
                        flags_state ->
                        exec_state -> exec_state -> Prop :=
| bes_apply:
  forall xstack new_xstack regs new_regs memory new_memory (in1: in_any) (in2:in_reg) (out: out_any)
    op1 op2 swap set_flags result flags_candidate flags new_flags ,

    fetch_apply21_swap swap
      (regs,memory,xstack)
      (in1, op1) (InReg in2, op2) (out, result)
      (new_regs,new_memory,new_xstack) ->
    new_flags = apply_set_flags set_flags flags flags_candidate ->
    binop_effect_spec
      swap set_flags
      (in1, op1) (in2, op2) (out, result)
      flags_candidate
      (mk_exec_state flags regs memory xstack)
      (mk_exec_state new_flags new_regs new_memory new_xstack).

