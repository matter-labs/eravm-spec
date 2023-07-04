From RecordUpdate Require Import RecordSet.

Require SemanticCommon Addressing.


Import ABI Addressing Bool Core Coder Common Condition CallStack GPR Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon MemoryContext Pointer PrimitiveValue State RecordSetNotations ZArith ZMod.

Import FatPointer.
Import List ListNotations.
Import Addressing.Coercions.


Section Defs.
 Open Scope ZMod_scope.

 Inductive step: instruction -> xsmallstep :=

(**
# Store

## Abstract Syntax

```
OpStore (ptr: in_regimm) (val: in_reg) (mem:data_page_type)
```

## Syntax

- `uma.heap_write in1, in2` aliased as `st.1 in1, out`
- `uma.aux_heap_write in1, in2` aliased as `st.2 in1, out`


## Summary

Store 32 consecutive bytes to the active `heap` or `aux_heap` page starting from
address `in1`.

## Semantic

1. Decode a fat pointer `in_ptr` from `ptr`.

   Fat pointers have following fields:

```
Record fat_ptr :=
  mk_fat_ptr {
      fp_page: page_id;
      fp_start: mem_address;
      fp_length: mem_address;
      fp_offset: mem_address;
    }.
```

2. Ensure storing 32 consecutive bytes is possible; it is impossible if $\texttt{fp\_offset} > 2^{32}-32$.

   Note: Valid (aux_)heap fat pointers always have `fp_start = 0`, therefore the read starts from an absolute address `fp_offset` in heap/auxheap. See [fat_ptr].

3. If  `fp_offset + 32 > (aux_)heap bound`, grow (aux_)heap bound and pay for the growth. We are aiming at reading a 256-bit word starting from address `fp_offset`, so the (aux_)heap bound should contain all of it.
4. Store 32 consecutive bytes of `val` as a Big Endian 256-bit word from address `fp_offset` in (aux_)heap.
*)

  | step_Store:
    forall flags new_cs heap_variant enc_ptr (arg_enc_ptr:in_regimm) (arg_val:in_reg) value new_regs new_mem selected_page in_ptr query modified_page cs regs mem __ ___,

      let selected_page_id := heap_variant_id heap_variant cs in

      loads _ regs cs mem [
         (in_regimm_incl arg_enc_ptr, mk_pv __ enc_ptr) ;
         (InReg          arg_val, mk_pv ___ value)
          ] cs ->

      ABI.(decode) enc_ptr = Some in_ptr ->

      (* In Heap/Auxheap, 'start' of the pointer is always 0, so offset = absolute address *)
      let addr := in_ptr.(fp_offset) in
      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      heap_variant_page heap_variant cs mem selected_page ->

      word_upper_bound in_ptr query ->
      grow_and_pay heap_variant query cs new_cs ->

      mb_store_word_result BigEndian selected_page addr value modified_page ->

      page_replace selected_page_id (@DataPage era_pages modified_page) mem new_mem ->

      step (OpStore arg_enc_ptr arg_val heap_variant)
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
(**
## Affected parts of VM state

- execution stack:

  + PC, as by any instruction;
  + ergs balance if the (aux_)heap has to be grown;
  + (aux_)heap bounds, if (aux_)heap has to be grown.

- GPRs, because `out` only resolves to a register.
- Memory page

## Usage

- Only [OpLoad] and [OpLoadInc] are capable of reading data from heap/aux_heap.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [OpLoad], [OpLoadInc], [OpStore], [OpStoreInc], [OpLoadPointer], [OpLoadPointerInc].

## Similar instructions

- [OpLoad], [OpLoadInc], [OpStore], [OpStoreInc], [OpLoadPointer], [OpLoadPointerInc] are variants of the same instruction.

 *)
End Defs.
