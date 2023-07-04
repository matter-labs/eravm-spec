From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Common CallStack Memory Instruction State ZMod
  ABI ABI.FatPointer Addressing.Coercions Coder PrimitiveValue Pointer SemanticCommon RecordSetNotations ZArith.

Section Def.
  Open Scope ZMod_scope.
(**

# PtrAdd

## Abstract Syntax

```
| OpPtrAdd      (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)
```

## Summary

Takes a fat pointer from `in1` and a 32-bit unsigned number from `in2`.
Advances the fat pointer's offset by that number, and writes the result to `out`.

## Semantic

1. Fetch input operands, swap them if `swap` modifier is set. Now operands are $\mathit{op_1}$ and $\mathit{op_2}$.
2. Ensure the $\mathit{op_1}$ is tagged as a pointer, and $\mathit{op_2}$ is not tagged as a pointer. Otherwise panic.
3. Decode fat pointer $\mathit{ptr_{in}}$ from $\mathit{op_1}$
4. Let $\mathit{diff}$ be $\mathit{op_2}$ truncated to 32 bits:

$$\mathit{diff} := \mathit{op}_2 \mod 2^{32}$$

5. Advance pointer offset of $\mathit{ptr_{in}}$ by $\mathit{diff}$:

$$\mathit{ptr_{out}} := \mathit{ptr_{in}} | _\mathit{offset := offset + diff}$$

6. Store the result, tagged as a pointer, to `out`:

$$result := \mathit{op_1}\{255\dots128\} || \texttt{encode}(\mathit{ptr_{out}})$$
 *)
Inductive step : instruction -> xsmallstep :=
| step_PtrAdd:
  forall (in1:in_any) (in2:in_reg) (out:out_any) op1 new_ofs op2 swap result ptr_in regs mem cs new_regs new_mem new_cs flags,

    fetch_apply21_swap swap (regs, mem, cs)

      (in1,PtrValue op1)
      (InReg in2, IntValue op2)
      (out,PtrValue result)

      (new_regs, new_mem, new_cs) ->

    FatPointer.ABI.(decode) op1 = Some ptr_in   ->
    let diff := resize _ 32 op2 in
    (new_ofs, false) = ptr_in.(fp_offset) + diff ->

    let ptr := FatPointer.ABI.(encode) (ptr_in <| fp_offset := new_ofs |>) in
    let low := resize _ 128 ptr in
    mix_lower 128 op1 low = result ->

    step (OpPtrAdd in1 in2 out swap)
         {|
           gs_callstack    := cs;
           gs_regs         := regs;
           gs_pages        := mem;


           gs_flags        := flags;
         |}
         {|
           gs_callstack    := new_cs;
           gs_regs         := new_regs;
           gs_pages        := new_mem;


           gs_flags        := flags;
         |}
.
(** ## Affected parts of VM state

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
End Def.
