Require  sem.SemanticCommon.

Import Addressing Bool ZArith Common Condition GPR Instruction CallStack Memory MemoryOps State ZMod
  ZBits Addressing.Coercions PrimitiveValue SemanticCommon List ListNotations.

Section Def.
  Open Scope Z_scope.

  Generalizable Variables arg_op arg_out any_tag .
  Inductive step_div: instruction -> xsmallstep :=
    
  (**
# Div

## Abstract Syntax

```
OpDiv (in1: in_any) (in2: in_reg) (out1: out_any) (out2: out_any)
      (swap:mod_swap) (flags:mod_set_flags)
```

## Syntax

- `div in1, in2, out1, out2`
- `div.s in1, in2, out1, out2`, to set `swap` modifier.
- `div! in1, in2, out1, out2`, to set `set flags` modifier.
- `div.s! in1, in2, out1, out2`, to set both `swap` and `set flags` modifiers.

## Summary

Unsigned division of two numbers. The quotient is returned in `out1`, the remainder is returned in `out2`.

## Semantic

- resolve `in1` and apply its addressing effects, resolve `in2`, resolve `out1` and apply its addressing effects, resolve `out2`.

- compute results of unsigned division of `in1` by `in2`.

1. If `in2` $\neq 0$:
   $$\begin{cases}out_1 := \frac{ op_1}{op_2} \\
out_{2} := \text{rem } op_1 \ op_2 \end{cases}$$

   Flags are computed as follows:
   - `LT_OF` is cleared;
   - `EQ` is cleared.
   - `GT` is cleared.

   Reminder: flags are only set if `set_flags` modifier is set.
   *) 
  | step_Div_no_overflow:
    
    forall (mod_swap: mod_swap) (mod_flags: mod_set_flags)
      (x y:Z) wx wy
      flags regs mem cs new_regs new_mem new_flags new_cs
      (quot rem: Z) wquot wrem,
      `(   
          fetch_apply22_swap mod_swap (regs,mem,cs)
                             
            (      arg_op1, mk_pv any_tag1 wx)
            (InReg arg_op2, mk_pv any_tag2 wy)

            (       arg_out1, IntValue wquot)
            (OutReg arg_out2, IntValue wrem)
            
            (new_regs, new_mem, new_cs) ->

          y <> 0 ->
          quot = Z.div x y ->
          rem = Z.rem x y ->

          let new_EQ := Z.eqb quot 0 in
          let new_GT := Z.eqb rem 0 in 
          new_flags = apply_set_flags mod_flags flags (bflags false new_EQ new_GT) ->
          
          step_div (OpDiv arg_op1 arg_op2 arg_out1 arg_out2 mod_swap mod_flags)
            (mk_exec_state flags regs mem cs)
            (mk_exec_state flags new_regs new_mem new_cs)
        )
  (**
2. If `in2` $= 0$:
   $$\begin{cases}out_1 := 0 \\
out_{2} := 0 \end{cases}$$

   Flags are computed as follows:
   - `LT_OF` is set.
   - `EQ` is set if $result_{low} = 0$.
   - `GT` is set if `LT_OF` and `EQ` are cleared.

Reminder: flags are only set if `set_flags` modifier is set.
   *)
  | step_Div_overflow:

    forall (mod_swap: mod_swap) (mod_flags: mod_set_flags)
      wx 
      flags regs mem cs new_regs new_mem new_flags new_cs,
      
      `(   
          fetch_apply22_swap mod_swap (regs,mem,cs)
                             
            (      arg_op1, mk_pv any_tag1 wx)
            (InReg arg_op2, mk_pv any_tag2 zero256)

            (       arg_out1, IntValue zero256)
            (OutReg arg_out2, IntValue zero256)
            
            (new_regs, new_mem, new_cs) ->
          
          new_flags = apply_set_flags mod_flags flags (bflags true false false) ->
          step_div (OpDiv arg_op1 arg_op2 arg_out1 arg_out2 mod_swap mod_flags)
            (mk_exec_state flags regs mem cs)
            (mk_exec_state flags new_regs new_mem new_cs)
        )
  .

(**
- Finally, store results in the locations corresponding to `out1` and `out2`.

## Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out1` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, by `out2` and `out1`, provided `out1` resolves to GPR.
- flags, if `set_flags` modifier is set.

## Usage

Arithmetic operations.

## Similar instructions

- See [OpMul].

 *)
End Def. 
