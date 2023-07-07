From RecordUpdate Require Import RecordSet.

Require SemanticCommon Addressing.

Import ABI Addressing Bool Common Coder Condition CallStack GPR Memory MemoryOps Instruction State ZMod
  Addressing.Coercions Pointer PrimitiveValue SemanticCommon MemoryContext State RecordSetNotations ZMod.

Import FatPointer.
Import List ListNotations.


Section Defs.

  Open Scope ZMod_scope.
  Import Pointer.Coercions.
  Generalizable Variables cs flags.
  Inductive step_load : instruction -> xsmallstep :=
    (**
# LoadInc

## Abstract Syntax

```
OpLoadInc (ptr: in_regimm) (res: out_reg) (mem:data_page_type) (inc_ptr: out_reg)
```

## Syntax

- `uma.inc.heap_read in1, out1, out2` aliased as `ld.1.inc in1, out1, out2`
- `uma.inc.aux_heap_read in1, out1, out2` aliased as `ld.2.inc in1, out1, out2`


## Summary

Load 32 consecutive bytes from address `ptr` of active `heap` or `aux_heap` page. Additionally, store a pointer to the next word to `inc_ptr` register.

## Semantic

1. Decode a fat pointer `in_ptr` from `ptr`

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

2. Ensure reading 32 consecutive bytes is possible; it is impossible if $\texttt{fp\_offset} > 2^{32}-32$.

   Note: Valid (aux_)heap fat pointers always have `fp_start = 0`, therefore the read starts from an absolute address `fp_offset` in heap/auxheap. See [fat_ptr].

3. If  `fp_offset + 32 > (aux_)heap bound`, grow (aux_)heap bound and pay for the growth. We are aiming at reading a 256-bit word starting from address `fp_offset`, so the (aux_)heap bound should contain all of it.
4. Read 32 consecutive bytes as a Big Endian 256-bit word from address `fp_offset` in (aux_)heap.
5. Store this word to `res`.
6. Store an encoded fat pointer to the next 32-byte word in (aux_)heap in `inc_ptr`. Its fields are assigned as follows:

```
fp_page := (aux_)heap page id;
fp_start := zero32;
fp_length := in_ptr.(fp_length);
fp_offset := in_ptr.(fp_offset) + 32;
```

*)
  | step_LoadInc:
    forall heap_variant enc_ptr (arg_dest arg_modptr:out_reg) (arg_enc_ptr:in_regimm) result mem new_regs selected_page ptr_inc query new_cs regs addr limit src_tag,
      `(
      load _  regs cs0 mem arg_enc_ptr (cs1, mk_pv src_tag enc_ptr) ->
      let hptr := mk_hptr addr limit in
      decode_heap_ptr enc_ptr = Some hptr ->

      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      heap_variant_page heap_variant cs1 mem selected_page ->
      mb_load_result BigEndian selected_page addr result ->

      word_upper_bound hptr query ->
      grow_and_pay heap_variant query cs1 new_cs ->

      hp_inc hptr ptr_inc ->
      let ptr_inc_enc := encode_fat_ptr (mk_fat_ptr None ptr_inc) in

      store_regs regs [
          (arg_dest, IntValue result);
          (arg_modptr, mk_pv src_tag ptr_inc_enc)
        ] new_regs ->

      step_load (OpLoadInc arg_enc_ptr arg_dest heap_variant arg_modptr)
        (mk_exec_state flags regs mem cs0)
        (mk_exec_state flags new_regs mem new_cs)
        )
  .
(**
## Affected parts of VM state

- execution stack:

  + PC, as by any instruction;
  + ergs balance if the (aux_)heap has to be grown;
  + (aux_)heap bounds, if (aux_)heap has to be grown.

- GPRs, because `res` and `inc_ptr` only resolve to registers.

## Usage

- Only [OpLoad] and [OpLoadInc] are capable of reading from (aux_)heapheap.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [OpLoad], [OpLoadInc], [OpStore], [OpStoreInc], [OpLoadPointer], [OpLoadPointerInc].

## Similar instructions

- [OpLoad], [OpLoadInc], [OpStore], [OpStoreInc], [OpLoadPointer], [OpLoadPointerInc] are variants of the same instruction.

 *)

End Defs.
