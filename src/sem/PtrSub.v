Require SemanticCommon.

Import
Core
Memory
MemoryBase
Pointer
PrimitiveValue
SemanticCommon
State
ZMod
isa.CoreSet
.

Section Def.
  Open Scope ZMod_scope.

  (**
# PtrSub

## Abstract Syntax

[%OpPtrSub (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)]

## Summary

Takes a fat pointer from `in1` and a 32-bit unsigned number from `in2`.
Rewinds the fat pointer's offset by that number, and writes the result to `out`.

## Semantic

1. Fetch input operands, swap them if `swap` modifier is set. Now operands are $\mathit{op_1}$ and $\mathit{op_2}$.
2. Ensure the $\mathit{op_1}$ is tagged as a pointer, and $\mathit{op_2}$ is not tagged as a pointer. Otherwise panic.
3. Decode fat pointer $\mathit{ptr_{in}}$ from $\mathit{op_1}$
4. Let $\mathit{diff}$ be $\mathit{op_2}$ truncated to 32 bits:

$$\mathit{diff} := \mathit{op}_2 \mod 2^{32}$$

5. Rewind pointer offset of $\mathit{ptr_{in}}$ by $\mathit{diff}$:

$$\mathit{ptr_{out}} := \mathit{ptr_{in}} | _\mathit{offset := offset - diff}$$

6. Store the result, tagged as a pointer, to `out`:

$$result := \mathit{op_1}\{255\dots128\} || \texttt{encode}(\mathit{ptr_{out}})$$

   *)
  Inductive step_ptrsub : instruction -> smallstep :=
  | step_PtrSub:
    forall src_enc result s ofs new_ofs pid (arg_delta:word) (mem_delta: mem_address) span,

      mem_delta = resize word_bits mem_address_bits arg_delta ->
      (new_ofs, false) = ofs + mem_delta ->

      topmost_128_bits_match src_enc result ->
      step_ptrsub (OpPtrSub
              (Some (mk_fat_ptr pid (mk_ptr span ofs)), PtrValue src_enc)
              (IntValue arg_delta)
              (mk_fat_ptr pid (mk_ptr span new_ofs), PtrValue result))
        s s
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

- Instruction [%OpPtrAdd] effectively performs the same actions but the offset is negated.

## Encoding

Instructions [%OpPtrAdd], [%OpPtrSub], [%OpPtrPack] and [%OpPtrShrink] are sharing an opcode.
 *)
End Def.
