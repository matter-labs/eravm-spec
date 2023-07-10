Require sem.BinOps.

Import Addressing Bool Common Flags Instruction Memory State ZMod
  Addressing.Coercions PrimitiveValue SemanticCommon BinOps.

Section Def.
  Open Scope ZMod_scope.
  Inductive step: instruction -> xsmallstep :=

  (**

## Sub

### Abstract Syntax

```
 | OpSub         (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
```

### Syntax

- `sub in1, in2, out`
- `sub.s in1, in2, out`, to set `swap` modifier.
- `sub! in1, in2, out`, to set `set flags` modifier.
- `sub.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Unsigned overflowing subtraction of two numbers modulo $2^{256}$.

### Semantic

Follows the scheme described in [binop_effect_spec].

Its parameter $F(op_1, op_2)$ is a function that acts as follows:

- result is computed by unsigned subtraction of two numbers with overflow modulo $2^{256}$.

   $$result := \begin{cases}op_1 - op_2 & , \text{if}\  op_1 \geq op_2\\ 2^{256} -  (op_2 - op_1) &, \text{if}\ op_1 \lt op_2\end{cases}$$

- flags are computed as follows:
   - `LT_OF` is set if overflow occurs, i.e. $op_1 \lt op_2$
   - `EQ` is set if $result = 0$.
   - `GT` is set if $op_1 \gt op_2$. An equivalent condition is: both `LT_OF` and `EQ` are cleared.

Reminder: flags are only set if `set_flags` modifier is set.

### Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.
- flags, if `set_flags` modifier is set.

### Usage

Arithmetic operations.

### Similar instructions

Flags are computed exactly as in `sub`, but the meaning of overflow is different for addition and subtraction.

   *)
  | step_Sub:
    forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out xs xs' _tag1 _tag2 op1 op2 result flags_candidate new_OF,

      binop_effect_spec mod_swap mod_sf
        (in1, mk_pv _tag1 op1)
        (in2, mk_pv _tag2 op2)
        (out, IntValue result) flags_candidate
        xs xs' ->

      (result, new_OF) = op1 - op2 ->
      let new_EQ := result == zero256 in
      let new_GT := negb new_EQ && negb new_OF in
      flags_candidate = bflags new_OF new_EQ new_GT ->

      step (OpSub in1 in2 out mod_swap mod_sf) xs xs'
  .
End Def.
