Require sem.Bitwise.
Import Addressing ZArith Common Instruction Memory ZMod
  Addressing.Coercions SemanticCommon PrimitiveValue sem.Bitwise.

Section Def.
  Open Scope ZMod_scope.
  Inductive step: instruction -> xsmallstep :=
  (**

## OR

### Abstract Syntax

[% OpOr (in1: in_any) (in2: in_reg) (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)]


### Syntax

- `or in1, in2, out`
- `or.s in1, in2, out`, to set `swap` modifier.
- `or! in1, in2, out`, to set `set flags` modifier.
- `or.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Bitwise OR of two 256-bit numbers.

### Semantic


Follows the scheme described in [%binop_effect_spec].

Its parameter $F(op_1, op_2)$ is a function that acts as follows:

- result is computed as a bitwise OR of two operands.
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
  | step_Or:
    forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out _tag1 _tag2 x y result gs gs',
      binop_bitwise_effect_spec in1 in2 out mod_swap mod_sf
        (mk_pv _tag1 x) (mk_pv _tag2 y) (IntValue result)  gs gs' ->
      result = bitwise_or _ x y ->
      step (OpOr in1 in2 out mod_swap mod_sf) gs gs'
  .
End Def.
