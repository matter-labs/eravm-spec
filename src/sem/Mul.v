From RecordUpdate Require Import RecordSet.
Require  sem.SemanticCommon.

Import Addressing Bool Core ZArith Common Flags Instruction CallStack Memory MemoryOps State ZMod
  ZBits  PrimitiveValue RecordSetNotations SemanticCommon List ListNotations.

Section Def.
  Open Scope ZMod_scope.

Inductive xstep: instruction -> xsmallstep :=
(**
# Mul

## Abstract Syntax

```
OpMul (in1: in_any) (in2: in_reg) (out1: out_any) (out2: out_any)
      (swap:mod_swap) (flags:mod_set_flags)
```

## Syntax

- `mul in1, in2, out1, out2`
- `mul.s in1, in2, out1, out2`, to set `swap` modifier.
- `mul! in1, in2, out1, out2`, to set `set flags` modifier.
- `mul.s! in1, in2, out1, out2`, to set both `swap` and `set flags` modifiers.

## Summary

Unsigned overflowing multiplication of two numbers modulo $2^{512}$; the high and low 256 bits of the result are returned in two separate operands.

## Semantic

1. Resolve `in1` and apply its addressing effects, resolve `in2`, resolve `out1` and apply its addressing effects, resolve `out2`.

2. Compute result by unsigned multiplication of `in1` by `in2`.

   $$\begin{cases}result_{high} := \frac{ op_1 \times op_2}{2^{256}}\\
result_{low} := op_1 \times op_2 \mod 2^{256} \end{cases}$$

3. Flags are computed as follows:
   - `LT_OF` is set if overflow occurs, i.e. $op_1 \times op_2 \geq 2^{256}$
   - `EQ` is set if $result_{low} = 0$.
   - `GT` is set if `LT_OF` and `EQ` are cleared.

   Reminder: flags are only set if `set_flags` modifier is set.

4. Wtore results in the locations corresponding to `out1` and `out2`.

## Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out1` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, by `out2` and `out1`, provided `out1` resolves to GPR.
- flags, if `set_flags` modifier is set.

## Usage

Arithmetic operations.

## Similar instructions

- See [%OpDiv].

 *)
  | step_Mul:
    forall flags pages cs regs (arg_op1:in_any) (arg_op2:in_reg) (arg_out1:out_any) (arg_out2:out_reg) any_tag1 any_tag2 mod_swap mod_flags wx wy wprod_high wprod_low (x y prod_high prod_low:Z) new_regs new_cs new_pages new_flags,
      fetch_apply22_swap mod_swap (regs,pages,cs)

        (      arg_op1, mk_pv any_tag1 wx)
        (InReg arg_op2, mk_pv any_tag2 wy)

        (       arg_out1, IntValue wprod_low)
        (OutReg arg_out2, IntValue wprod_high)

        (new_regs, new_pages, new_cs) ->
      wx = u256_of x -> wy = u256_of y ->
      wprod_low = u256_of prod_low ->
      wprod_high = u256_of prod_high ->
      extract_digits (x * y) word_bits 2 = [ prod_high;  prod_low ] ->

      let new_EQ := wprod_low  == zero256 in
      let new_OF := wprod_high != zero256 in
      let new_GT := (negb new_OF) && (negb new_EQ) in
      new_flags = apply_set_flags mod_flags flags (bflags new_OF new_EQ new_GT) ->

      xstep (OpMul arg_op1 arg_op2 arg_out1 arg_out2 mod_swap mod_flags)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_callstack    := cs;
          gs_pages        := pages;
        |}
        {|
          gs_flags        := new_flags;
          gs_regs         := new_regs;
          gs_callstack    := new_cs;
          gs_pages        := new_pages;
        |}
.

End Def.
