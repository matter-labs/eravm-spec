From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Bool Common Condition ExecutionStack Memory MemoryOps Instruction State ZMod
  ABI ABI.FatPointer Arg Arg.Coercions SemanticCommon RecordSetNotations ZArith.

Definition MAX_OFFSET_FOR_ADD_SUB: u256 := int_mod_of _ (2^32)%Z.



(** # Pointer manipulation instructions

Fat pointers can be manipulated by following instructions:

- [OpPtrAdd]
- [OpPtrSub]
- [OpPtrShrink]
- [OpPtrPack]

 *)


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
Inductive step : instruction -> smallstep :=
| step_PtrAdd:
  forall (in1:in_any) (in2:in_reg) (out:out_any) op1 new_ofs op2 swap flags result xstack0 new_xstack regs pages new_pages new_regs codes context_u128 depot ptr_in,
    
    fetch_apply2_swap swap (regs, xstack0, pages)
      in1 in2 out
      (PtrValue op1) (IntValue op2) (PtrValue result)
      (new_regs, new_xstack, new_pages) ->
    
    FatPointer.ABI.(decode) op1 = Some ptr_in   ->
    let diff := resize _ 32 op2 in
    (new_ofs, false) = ptr_in.(fp_offset) + diff ->

    let ptr := FatPointer.ABI.(encode) (ptr_in <| fp_offset := new_ofs |>) in
    let low := resize _ 128 ptr in
    mix_lower 128 op1 low = result ->
    
    step (OpPtrAdd in1 in2 out swap)
         {|
           gs_callstack    := xstack0;
           gs_regs         := regs;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_depot        := depot;
           gs_contracts    := codes;
         |}
         {|
           gs_callstack    := new_xstack;
           gs_regs         := new_regs;
           gs_pages        := new_pages;
           
           
           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_depot        := depot;
           gs_contracts    := codes;
         |}

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

# PtrSub

## Abstract Syntax

```
| OpPtrSub (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)

```

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

| step_PtrSub:
  forall (in1:in_any) (in2:in_reg) (out:out_any) op1 page start length ofs new_ofs op2 swap flags result xstack0 new_xstack regs pages new_pages new_regs codes context_u128 depot,
    
    fetch_apply2_swap swap (regs, xstack0, pages)
      in1 in2 out
      (PtrValue op1) (IntValue op2) (PtrValue result)
      (new_regs, new_xstack, new_pages) ->
    
    FatPointer.ABI.(decode) op1 = Some (mk_fat_ptr page start length ofs)  ->
    let diff := resize _ 32 op2 in 
    (new_ofs, false) = ofs - diff  ->


    let ptr := FatPointer.ABI.(encode) (mk_fat_ptr page start length new_ofs) in
    let low := resize _ 128 ptr in
    mix_lower 128 op1 low = result ->
    
    step (OpPtrSub in1 in2 out swap)
         {|
           gs_callstack    := xstack0;
           gs_regs         := regs;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_depot        := depot;
           gs_contracts    := codes;
         |}
         {|
           gs_callstack    := new_xstack;
           gs_regs         := new_regs;
           gs_pages        := new_pages;
           
           
           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_depot        := depot;
           gs_contracts    := codes;
         |}
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

- Instruction [OpPtrAdd] effectively performs the same actions but the offset is negated.

## Encoding

Instructions [OpPtrAdd], [OpPtrSub], [OpPtrPack] and [OpPtrShrink] are sharing an opcode.


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
  forall (in1:in_any) (in2:in_reg) (out:out_any) op1 op2 swap flags xstack new_xstack regs pages new_pages new_regs codes context_u128 depot,
    
    fetch_apply2_swap swap (regs, xstack, pages)
      in1 in2 out
      (PtrValue op1) (IntValue op2) (PtrValue (mix_lower 128 op2 (resize _ 128 op1)))
      (new_regs, new_xstack, new_pages) ->
    
    resize _ 128 op2 = zero128 ->
    
    step (OpPtrPack in1 in2 out swap)
         {|
           gs_callstack    := xstack;
           gs_regs         := regs;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_depot        := depot;
           gs_contracts    := codes;
         |}
         {|
           gs_callstack    := new_xstack;
           gs_regs         := new_regs;
           gs_pages        := new_pages;
           
           
           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_depot        := depot;
           gs_contracts    := codes;
         |}
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
  forall (in1:in_any) (in2:in_reg) (out:out_any) op1 op2 swap flags xstack new_xstack regs pages new_pages new_regs codes context_u128 depot result ptr_in ptr_out,
    
    fetch_apply2_swap swap (regs, xstack, pages)
      in1 in2 out
      (PtrValue op1) (IntValue op2) (PtrValue result)
      (new_regs, new_xstack, new_pages) ->
    
    FatPointer.ABI.(decode) op1 = Some ptr_in ->

    let diff := resize _ 32 op2 in
    fat_ptr_trim_length ptr_in diff  ptr_out ->
      
    let res_low := resize _ 128 (FatPointer.ABI.(encode) ptr_out) in
    result = mix_lower 128 op1 res_low ->
                   
    step (OpPtrPack in1 in2 out swap)
         {|
           gs_callstack    := xstack;
           gs_regs         := regs;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_depot        := depot;
           gs_contracts    := codes;
         |}
         {|
           gs_callstack    := new_xstack;
           gs_regs         := new_regs;
           gs_pages        := new_pages;
           
           
           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_depot        := depot;
           gs_contracts    := codes;
         |}
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

