From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Common CallStack Memory Instruction State ZMod
  ABI ABI.FatPointer Addressing.Coercions SemanticCommon RecordSetNotations ZArith.

Inductive step: instruction -> smallstep :=
(** 
# PtrShrink

## Abstract Syntax

```
| OpPtrShrink   (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)
```

## Summary


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
  forall (in1:in_any) (in2:in_reg) (out:out_any) op1 op2 swap result ptr_in ptr_out regs mem xstack new_regs new_mem new_xstack flags s1 s2,
    
    fetch_apply2_swap swap
      (regs, mem, xstack)
      in1 in2 out
      (PtrValue op1) (IntValue op2) (PtrValue result)
      (new_regs, new_mem, new_xstack) ->
    
    FatPointer.ABI.(decode) op1 = Some ptr_in ->

    let diff := resize _ 32 op2 in
    fat_ptr_trim_length ptr_in diff  ptr_out ->
      
    let res_low := resize _ 128 (FatPointer.ABI.(encode) ptr_out) in
    result = mix_lower 128 op1 res_low ->

    step_xstate
      (mk_exec_state flags regs mem xstack)
      (mk_exec_state flags new_regs new_mem new_xstack)
      s1 s2 ->
    step (OpPtrPack in1 in2 out swap) s1 s2
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
   - [OpPtrAdd]
   - [OpPtrSub]
   - [OpPtrShrink]
   - [OpPtrPack]


## Encoding

Instructions [OpPtrAdd], [OpPtrSub], [OpPtrPack] and [OpPtrShrink] are sharing an opcode.
*)
