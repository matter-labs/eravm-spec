Require sem.Bitwise.
Import Addressing ZArith Common Instruction Memory ZMod
  Addressing.Coercions SemanticCommon sem.Bitwise.

Section Def.
  Open Scope ZMod_scope.
  Inductive step: instruction -> smallstep :=
  (**

## Shl

### Abstract Syntax

```
 | OpShl (in1: in_any) (in2: in_reg) (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
```

### Syntax

- `shl in1, in2, out`
- `shl.s in1, in2, out`, to set `swap` modifier.
- `shl! in1, in2, out`, to set `set flags` modifier.
- `shl.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Bitwise left shift of `in1` by the number of binary digits specified by `in2`, but no more than 256. New binary digits (least significant bits) are zeros.

### Semantic

Follows the scheme described in [binop_state_bitwise_effect_spec].

- result is computed as a bitwise XOR of two operands. 
- flags are computed as follows:
   - `EQ` is set if $result = 0$.
   - `OF_LT` and `GT` are cleared

Reminder: flags are only set if `set_flags` modifier is set.

### Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.
- flags, if `set_flags` modifier is set.

### Usage

- operations with bit masks

### Similar instructions

- `and`, `or` and `xor` are encoded as variants of the same instruction.

   *)
  | step_Shl:
    forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out _tag1 _tag2 x y result gs gs',
      binop_state_bitwise_effect_spec in1 in2 out mod_swap mod_sf
        (mk_pv _tag1 x) (mk_pv _tag2 y) (IntValue result)  gs gs' ->
      result = shiftl _ x y ->
      step (OpShl in1 in2 out mod_sf) gs gs'
  .

End Def.
