From RecordUpdate Require Import RecordSet.
Require  sem.SemanticCommon.

Import Addressing Bool ZArith Common Condition Instruction CallStack Memory MemoryOps State ZMod
  ZBits Addressing.Coercions RecordSetNotations SemanticCommon List ListNotations.

Local Coercion u256_of : Z >-> int_mod.

Inductive step: instruction -> smallstep :=
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

Unsigned overflowing multiplication of two numbers modulo $2^{512}$; the high and low 256 bits of the result is returned in two separate operands.

## Semantic

- resolve `in1` and apply its addressing effects, resolve `in2`, resolve `out1` and apply its addressing effects, resolve `out2`.

- compute result by unsigned multiplication of `in1` by `in2`.

   $$\begin{cases}result_{high} := \frac{ op_1 \times op_2}{2^{256}}\\
result_{low} := op_1 \times op_2 \mod 2^{256} \end{cases}$$

- flags are computed as follows:
   - `LT_OF` is set if overflow occurs, i.e. $op_1 \times op_2 \geq 2^{256}$
   - `EQ` is set if $result_{low} = 0$.
   - `GT` is set if `LT_OF` and `EQ` are cleared.

Reminder: flags are only set if `set_flags` modifier is set.

- store results in the locations corresponding to `out1` and `out2`.

## Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out1` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, by `out2` and `out1`, provided `out1` resolves to GPR.
- flags, if `set_flags` modifier is set.

## Usage

Arithmetic operations.

## Similar instructions

- See [OpDiv].

 *)
  | step_Mul:
    forall flags pages xstack regs (arg_op1:in_any) (arg_op2:in_reg) (arg_out1:out_any) (arg_out2:out_reg) any_tag1 any_tag2 mod_swap mod_flags (x y prod_high prod_low:Z) new_regs new_xstack new_pages new_flags s1 s2,
      fetch_apply22_swap mod_swap (regs,pages,xstack)
                     arg_op1 arg_op2
                     arg_out1 arg_out2
                     (mk_pv any_tag1 x) (mk_pv any_tag2 y) (IntValue prod_low, IntValue prod_high)
                     (new_regs,new_pages,new_xstack) ->

      extract_digits (x * y) word_bits 2 = [ prod_high;  prod_low ] -> 

      let new_EQ := prod_low  == zero256 in
      let new_OF := prod_high != zero256 in
      let new_GT := (negb new_OF) && (negb new_EQ) in 
      new_flags = apply_set_flags mod_flags flags (bflags new_OF new_EQ new_GT) ->

      step_xstate
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_callstack    := xstack;
          gs_pages        := pages;
        |}
        {|
          gs_flags        := new_flags;
          gs_regs         := new_regs;
          gs_callstack    := new_xstack;
          gs_pages        := new_pages;
        |} s1 s2 ->
      step (OpMul arg_op1 arg_op2 arg_out1 arg_out2 mod_swap mod_flags) s1 s2
.
