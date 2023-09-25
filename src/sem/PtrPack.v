Require SemanticCommon.

Import Common Core Memory isa.CoreSet State
  SemanticCommon PrimitiveValue ZArith FatPointerABI.

Section PtrPackDefinition.
  Open Scope ZMod_scope.
  Inductive step_ptrpack : instruction -> smallstep :=
  (** # PtrPack

## Abstract Syntax

[%OpPtrPack (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)]

## Syntax

- `ptr.pack in1, in2, ou1`
- `ptr.pack.s in1, in2, ou1`

## Summary

Concatenates the lower 128 bit of `in1` and the higher 128 bits of `in2`, writes result to `out`.
`in1` should hold a [%fat_ptr].

See Usage.

## Semantic

1. Fetch input operands, swap them if `swap` modifier is set. Now operands are $\mathit{op_1}$ and $\mathit{op_2}$.
2. Ensure the $\mathit{op_1}$ is tagged as a pointer, and $\mathit{op_2}$ is not tagged as a pointer. Otherwise panic.
3. Ensure that the lower 128 bits of $\mathit{op}_2$ are zero. Otherwise panic.
4. Store the result, tagged as a pointer, to `out`:

$$result := \mathit{op_1}\{255\dots128\} \#\# \mathit{op_2}\{128\dots 0\}$$
   *)

  | step_PtrPack :
    forall op1_high128 ptr (op2:word) (s:state) encoded result,
      low 128 op2 = zero128 ->
      Some encoded = encode_fat_ptr ptr ->
      result = (@high 128 128 op2) ## encoded ->
      step_ptrpack (@OpPtrPack bound (Some (PtrValue (op1_high128, ptr))) (IntValue op2) (IntValue result)) s s
(** ## Affected parts of VM state
- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.


- Flags are unaffected

## Usage

- fat pointer in $in_1$ spans across bits $in_1{0\dots127}$, and the bits
  $in_1{128\dots255}$ are therefore available to put other data.
  This is used by for memory forwarding to far calls when we need to forward an existing fat pointer.

  To pass a fat pointer `P` to far call, it is necessary to encode an instance of
  [%ABI.FarCall.params] with [%fwd_memory := ForwardFatPointer P] into a
  [%PtrValue].

  ```
  Module ABI.FarCall.

  Record params :=
    mk_params {
        fwd_memory: fwd_memory;
        ergs_passed: ergs;
        shard_id: shard_id;
        constructor_call: bool;
        to_system: bool;
      }.
  ```

  The compound type [%ABI.FarCall.params] is serialized to a [%word] in such a
  way that the pointer takes up the lower 128 bits of memory.
  This matches the layout of any fat pointer: serialized pointers occupy the
  lower 128 bit of a word.

  Therefore, encoding an instance of [%ABI.FarCall.params] can be done as follows:

  - take an existing [%PtrValue P]
  - form a value `A` encoding [%ergs_passed], [%shard_id] and other fields of
    [%ABI.FarCall.params] in A{128...255}.
  - invoke [%OpPtrPack P A B]. Now `B` stores an encoded instance of
    [%ABI.FarCall.params] and can be passed to one of far call instructions.

## Similar instructions

- Takes part in a group of pointer manipulating instructions:
   - [%OpPtrAdd]
   - [%OpPtrSub]
   - [%OpPtrShrink]
   - [%OpPtrPack]

## Encoding

Instructions [%OpPtrAdd], [%OpPtrSub], [%OpPtrPack] and [%OpPtrShrink] are sharing an opcode.

## Panics

1. First argument is not a pointer (after accounting for `swap`).
 *)
  | step_PtrPack_in1_not_ptr:
    forall s1 s2 ___1 ___2 ___3,
      step_panic ExpectedFatPointer s1 s2 ->
      step_ptrpack (OpPtrPack (Some (IntValue ___1)) ___2 ___3) s1 s2
  (** 2. Second argument is a pointer (after accounting for `swap`). *)
  | step_PtrPack_in2_ptr:
    forall s1 s2 ___1 ___2 ___3,
      step_panic ExpectedFatPointer s1 s2 ->
      step_ptrpack (OpPtrPack (Some ___1) (PtrValue ___2) ___3) s1 s2
  (** 3. Low 128 bits of the second operand are not zero (after accounting for `swap`). *)
  | step_PtrPack_notzero:
    forall s1 s2 op2 ___1 ___2,

      low 128 op2 <> zero128 ->
      step_panic PtrPackExpectsOp2Low128BitsZero s1 s2 ->
      step_ptrpack (@OpPtrPack bound ___1 (IntValue op2) ___2) s1 s2
  .

End PtrPackDefinition.
