From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Common CallStack Memory Instruction State ZMod
  ABI ABI.FatPointer Addressing.Coercions SemanticCommon RecordSetNotations ZArith.

Inductive step : instruction -> smallstep :=
(**
# PtrPack

## Abstract Syntax

```
| OpPtrPack (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)

```

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
  forall (in1:in_any) (in2:in_reg) (out:out_any) op1 op2 swap s1 s2 regs mem xstack new_regs new_mem new_xstack flags,
    
    fetch_apply2_swap swap
      (regs, mem, xstack)
      in1 in2 out
      (PtrValue op1) (IntValue op2) (PtrValue (mix_lower 128 op2 (resize _ 128 op1)))
      (new_regs, new_mem, new_xstack) ->
    
    resize _ 128 op2 = zero128 ->
    step_xstate
      (mk_exec_state flags regs mem xstack)
      (mk_exec_state flags new_regs new_mem new_xstack)
      s1 s2 ->
    step (OpPtrPack in1 in2 out swap) s1 s2.
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
   - [OpPtrAdd]
   - [OpPtrSub]
   - [OpPtrShrink]
   - [OpPtrPack]

- Instruction [OpPtrSub] effectively performs the same actions but the offset is negated.

## Encoding

Instructions [OpPtrAdd], [OpPtrSub], [OpPtrPack] and [OpPtrShrink] are sharing an opcode.

*)
