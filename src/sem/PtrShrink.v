Require SemanticCommon.

Import Common Core Memory isa.CoreSet State
  Pointer PrimitiveValue SemanticCommon ZArith.

Section PtrShrinkDefinition.
  Open Scope ZMod_scope.

  Inductive step_ptrshrink: instruction -> smallstep :=
  (** # PtrShrink

**Attention**: **shrinking** and **narrowing** far pointers are different. See
  [%fat_ptr_shrink] and [%fat_ptr_narrow].

## Abstract Syntax

[%OpPtrShrink   (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)]

## Syntax

- `ptr.shrink in1, in2, ou1`
- `ptr.shrink.s in1, in2, ou1`

## Summary

**Shrink** the fat pointer, decreasing its length.

## Semantic

1. Fetch input operands, swap them if `swap` modifier is set. Now operands are $\mathit{op_1}$ and $\mathit{op_2}$.
2. Ensure the $\mathit{op_1}$ is tagged as a pointer, and $\mathit{op_2}$ is not tagged as a pointer. Otherwise panic.
3. Decode fat pointer $\mathit{ptr_{in}}$ from $\mathit{op_1}$
4. Let $\mathit{diff}$ be $\mathit{op_2}$ truncated to 32 bits:

$$\mathit{diff} := \mathit{op}_2 \mod 2^{32}$$

5. Rewind pointer length of $\mathit{ptr_{in}}$ by $\mathit{diff}$:

$$\mathit{ptr_{out}} := \mathit{ptr_{in}} | _\mathit{length := length - diff}$$

6. Store the result, tagged as a pointer, to `out`:

$$result := \mathit{op_1}\{255\dots128\} || \texttt{encode}(\mathit{ptr_{out}})$$
   *)

  | step_PtrShrink :
    forall  s result ptr_in ptr_out src_enc delta ,

      let diff := low mem_address_bits delta in
      fat_ptr_shrink diff ptr_in ptr_out ->


      topmost_128_bits_match src_enc result ->
      step_ptrshrink (OpPtrShrink
                        (Some ptr_in, PtrValue src_enc)
                        (IntValue delta)
                        (ptr_out, PtrValue result))
        s s
(** ## Affected parts of VM state

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


## Encoding

Instructions [%OpPtrAdd], [%OpPtrSub], [%OpPtrPack] and [%OpPtrShrink] are sharing an opcode.

## Panic

1. First argument is not a pointer (after accounting for `swap`).
 *)
  | step_PtrShrink_in1_not_ptr:
    forall s1 s2 ___1 ___2 ___3 ___4,
      step_panic ExpectedFatPointer s1 s2 ->
      step_ptrshrink (OpPtrShrink (Some ___1, IntValue ___2) ___3 ___4) s1 s2
  (** 2. Second argument is a pointer (after accounting for `swap`). *)
  | step_PtrShrink_in2_ptr:
    forall s1 s2 ___1 ___2 ___3 ___4,
      step_panic ExpectedFatPointer s1 s2 ->
      step_ptrshrink (OpPtrShrink (Some ___1, ___2) (PtrValue ___3) ___4) s1 s2
  (** 3. Shrinking underflows. *)
  | step_PtrShrink_underflow:
    forall s1 s2 result ptr_in ptr_out src_enc delta ,
      let diff := low mem_address_bits delta in
      fat_ptr_shrink_OF diff ptr_in = None ->

      step_ptrshrink (OpPtrShrink
                        (Some ptr_in, PtrValue src_enc)
                        (IntValue delta)
                        (ptr_out, PtrValue result))
        s1 s2
  .
End PtrShrinkDefinition.
