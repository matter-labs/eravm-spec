Require SemanticCommon.

Import
  Arith
Core
Memory
MemoryBase
Pointer
PrimitiveValue
SemanticCommon
State
isa.CoreSet
.
Import spec.

Section PtrSubDefinition.
  Open Scope ZMod_scope.
  (** # PtrSub

## Abstract Syntax

[%OpPtrSub (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)]

## Syntax

- `ptr.sub in1, in2, out`
- `ptr.sub.s in1, in2, out`

## Summary

Takes a fat pointer from `in1` and a 32-bit unsigned number from `in2`. Advances
the fat pointer's offset by that number, and writes (`in2`{128...255} ||
incremented pointer) to `out`.

## Semantic

1. Fetch input operands, swap them if `swap` modifier is set. Now operands are
   $\mathit{op_1}$ and $\mathit{op_2}$.
2. Ensure the $\mathit{op_1}$ is tagged as a pointer, and $\mathit{op_2}$ is not
   tagged as a pointer. Otherwise panic.
3. Decode fat pointer $\mathit{ptr_{in}}$ from $\mathit{op_1}$
4. Let $\mathit{diff}$ be $\mathit{op_2}$ truncated to 32 bits:

   $$\mathit{diff} := \mathit{op}_2 \mod 2^{32}$$

   It is required that $\mathit{op}_2< \texttt{MAX\_OFFSET\_FOR\_ADD\_SUB}$,
   otherwise VM panics.

5. Advance pointer offset of $\mathit{ptr_{in}}$ by $\mathit{diff}$:

$$\mathit{ptr_{out}} := \mathit{ptr_{in}} | _\mathit{offset := offset - diff}$$

6. Store the result, tagged as a pointer, to `out`. The most significant 128 bits of result are taken from `op1`, the least significant bits hold an encoded pointer:

$$result := \mathit{op_1}\{255\dots128\} \#\# \texttt{encode}(\mathit{ptr_{out}})$$

   *)
  Inductive step_ptrsub : instruction -> smallstep :=
  | step_PtrSub:
    forall high128 s ofs new_ofs pid (arg_delta:word) (mem_delta: mem_address) span,

      arg_delta <= MAX_OFFSET_FOR_ADD_SUB = true->
      mem_delta = low mem_address_bits arg_delta ->
      (false,new_ofs) = ofs - mem_delta ->

      step_ptrsub (OpPtrSub
              (Some (PtrValue (high128, NotNullPtr (mk_fat_ptr pid (mk_ptr span ofs)))))
              (IntValue arg_delta)
              (Some (PtrValue (high128, NotNullPtr (mk_fat_ptr pid (mk_ptr span new_ofs))))))
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

- Instruction [%OpPtrSub] effectively performs the same actions but the offset is added, not subtracted.

## Encoding

Instructions [%OpPtrSub], [%OpPtrSub], [%OpPtrPack] and [%OpPtrShrink] are sharing an opcode.

## Panics

1. First argument is not a pointer (after accounting for `swap`).
 *)
  | step_PtrSub_in1_not_ptr:
    forall s1 s2 ___ ____ _____,
      step_panic ExpectedFatPointer s1 s2 ->
      step_ptrsub (OpPtrSub (Some (IntValue ___)) ____ _____) s1 s2
  (** 2. Second argument is a pointer (after accounting for `swap`). *)
  | step_PtrSub_in2_ptr:
    forall s1 s2 __ ____ _____,
      step_panic ExpectedFatPointer s1 s2 ->
      step_ptrsub (OpPtrSub __ (PtrValue ____) _____) s1 s2

  (** 3. Second argument is larger than [%MAX_OFFSET_FOR_SUB_SUB] (after
  accounting for `swap`). *)
  | step_PtrSub_diff_too_large:
    forall s1 s2 (arg_delta:word) (mem_delta: mem_address) ___ ____,

      arg_delta >= MAX_OFFSET_FOR_ADD_SUB = true ->
      step_panic FatPointerDeltaTooLarge s1 s2 ->
      step_ptrsub (OpPtrSub (Some (PtrValue ___)) (IntValue arg_delta) ____) s1 s2
  (** 4. Subtraction underflows. *)
  | step_PtrSub_underflow:
    forall high128 s1 s2 ofs new_ofs pid (arg_delta:word) (mem_delta: mem_address) span,

      arg_delta < MAX_OFFSET_FOR_ADD_SUB = true ->
      mem_delta = low mem_address_bits arg_delta ->
      (true, new_ofs) = ofs - mem_delta ->

      step_panic FatPointerOverflow s1 s2 ->
      step_ptrsub (OpPtrSub
                     (Some (PtrValue (high128, NotNullPtr (mk_fat_ptr pid (mk_ptr span ofs)))))
                     (IntValue arg_delta)
                     (Some (PtrValue (high128, NotNullPtr (mk_fat_ptr pid (mk_ptr span new_ofs))))))

        s1 s2
  .
End PtrSubDefinition.
