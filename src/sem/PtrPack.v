Require SemanticCommon.

Import Addressing Addressing.Coercions Common CallStack Memory Instruction State ZMod
  ABI ABI.FatPointer Addressing.Coercions SemanticCommon PrimitiveValue ZArith.

Section Def.
  Open Scope ZMod_scope.
Inductive step : instruction -> xsmallstep :=
(**
# PtrPack

## Abstract Syntax

[%OpPtrPack (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)]

## Summary

Concatenates the upper 128 bit of `in1` and the lower 128 bits of `in2`.


## Semantic

1. Fetch input operands, swap them if `swap` modifier is set. Now operands are $\mathit{op_1}$ and $\mathit{op_2}$.
2. Ensure the $\mathit{op_1}$ is tagged as a pointer, and $\mathit{op_2}$ is not tagged as a pointer. Otherwise panic.
3. Ensure that the lower 128 bits of $\mathit{op}_2$ are zero. Otherwise panic.
4. Store the result, tagged as a pointer, to `out`:

$$result := \mathit{op_1}\{255\dots128\} || \mathit{op_2}\{128\dots 0\}$$
 *)

| step_PtrPack :
  forall (in1:in_any) (in2:in_reg) (out:out_any) op1 op2 swap regs mem cs new_regs new_mem new_cs flags,

    fetch_apply21_swap swap
      (regs, mem, cs)
      (in1, PtrValue op1) (InReg in2, IntValue op2) (out, PtrValue (mix_lower 128 op2 (resize _ 128 op1)))
      (new_regs, new_mem, new_cs) ->

    resize _ 128 op2 = zero128 ->
    step (OpPtrPack in1 in2 out swap)
      (mk_exec_state flags regs mem cs)
      (mk_exec_state flags new_regs new_mem new_cs)
.
(**

## Affected parts of VM state
- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.


- Flags are unaffected

## Usage

- Manipulating fat pointers to pass slices of memory between functions.

## Similar instructions

- Takes part in a group of pointer manipulating instructions:
   - [%OpPtrAdd]
   - [%OpPtrSub]
   - [%OpPtrShrink]
   - [%OpPtrPack]

- Instruction [%OpPtrSub] effectively performs the same actions but the offset is negated.

## Encoding

Instructions [%OpPtrAdd], [%OpPtrSub], [%OpPtrPack] and [%OpPtrShrink] are sharing an opcode.

*)
End Def.
