Require SemanticCommon.

Import Common Core Memory isa.CoreSet State ZMod
  SemanticCommon PrimitiveValue ZArith.

Section PtrPack.
  Open Scope ZMod_scope.
  Inductive step_ptrpack : instruction -> smallstep :=
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
    forall (op1 op2:word) (s:state) result __,

      resize _ 128 op2 = zero128 ->
      result = mix_lower 128 op2 (resize _ 128 op1) ->
      step_ptrpack (@OpPtrPack bound (Some __, PtrValue op1) (IntValue op2) (IntValue result)) s s
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
End PtrPack.
