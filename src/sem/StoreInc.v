From RecordUpdate Require Import RecordSet.

Require SemanticCommon Addressing.


Import ABI Addressing Bool Core Coder Common Condition CallStack GPR Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon MemoryContext Pointer PrimitiveValue State RecordSetNotations ZArith ZMod.

Import FatPointer.
Import List ListNotations.
Import Addressing.Coercions.


Section Defs.
 Open Scope ZMod_scope.
 Import Pointer.Coercions.
 Inductive step: instruction -> xsmallstep :=
(**
# StoreInc

## Abstract Syntax

```
OpStoreInc (ptr: in_regimm) (val: in_reg) (mem:data_page_type) (inc_ptr: out_reg)
```

## Syntax

- `uma.inc.heap_write in1, in2` aliased as `st.1.inc in1, out`
- `uma.inc.aux_heap_write in1, in2` aliased as `st.2.inc in1, out`


## Summary

Store 32 consecutive bytes to the active `heap` or `aux_heap` page starting from
address `ptr`. Additionally, store a pointer to the next word to `art_ptr` register.

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
5. Store an encoded fat pointer to the next 32-byte word in (aux_)heap in `inc_ptr`. Its fields are assigned as follows:

```
fp_page := (aux_)heap page id;
fp_start := zero32;
fp_length := in_ptr.(fp_length);
fp_offset := in_ptr.(fp_offset) + 32;
```
*)
  | step_StoreInc:
    
    forall flags new_cs heap_variant enc_ptr (arg_enc_ptr:in_regimm) (arg_val:in_reg) value new_regs new_mem selected_page query modified_page cs regs mem __ ___ addr limit arg_modptr hptr_mod,

      let selected_page_id := heap_variant_id heap_variant cs in

      loads _ regs cs mem [
         (in_regimm_incl arg_enc_ptr, mk_pv __ enc_ptr) ;
         (InReg          arg_val, mk_pv ___ value)
          ] cs ->

      let hptr := mk_hptr addr limit in
      decode_heap_ptr enc_ptr = Some hptr ->

      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      heap_variant_page heap_variant cs mem selected_page ->

      word_upper_bound hptr query ->
      grow_and_pay heap_variant query cs new_cs ->

      mb_store_word_result BigEndian selected_page addr value modified_page ->
      page_replace selected_page_id (@DataPage era_pages modified_page) mem new_mem ->

      hptr_inc hptr hptr_mod ->
      let ptr_inc_enc := encode_fat_ptr (mk_fat_ptr None hptr_mod) in

      step (OpStoreInc arg_enc_ptr arg_val heap_variant arg_modptr)
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
                 |}.
(**
## Affected parts of VM state

- execution stack:

  + PC, as by any instruction;
  + ergs balance if the (aux_)heap has to be grown;
  + (aux_)heap bounds, if (aux_)heap has to be grown.

- GPRs, because `res` and `inc_ptr` only resolve to registers.

## Usage

- Only [OpStore] and [OpStoreInc] are capable of writing to (aux_)heap.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [OpLoad], [OpLoadInc], [OpStore], [OpStoreInc], [OpLoadPointer], [OpLoadPointerInc].

## Similar instructions

- [OpLoad], [OpLoadInc], [OpStore], [OpStoreInc], [OpLoadPointer], [OpLoadPointerInc] are variants of the same instruction.

 *)
End Defs.
