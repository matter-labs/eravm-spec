Require SemanticCommon Addressing.


Import ABI Addressing Common Condition CallStack Memory MemoryOps Instruction ZMod
  Addressing.Coercions SemanticCommon Pages State ZMod.

Import FatPointer.
Import List ListNotations.


Section Defs.
  
  Context (old_regs: regs_state) (old_xstack: callstack) (old_pages:memory).
  Let fetch := resolve_load old_xstack (old_regs, old_pages).
  Let fetch_word := resolve_load_word old_xstack (old_regs,old_pages).
  Let stores := resolve_stores old_xstack (old_regs,old_pages).
  
  (**
# LoadPointer


## Abstract Syntax

```
OpLoadPointerInc (ptr: in_reg)  (res: out_reg) (inc_ptr: out_reg)
```

## Syntax

- `uma.fat_ptr_read.inc in1, out` aliased as `ld.inc in1, out`


## Summary

Read 32 consecutive bytes from address `ptr` of active `heap` or `aux_heap` page as a 256-bit word, Big Endian. Reading bytes past the slice bound yields zero bytes.

Additionally, store a pointer to the next word to `inc_ptr` register.

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

2. Validate that offset is in bounds: `fp_offset < fp_length`.

3. Read 32 consecutive bytes as a Big Endian 256-bit word from address `fp_offset` in (aux_)heap.

   Reading bytes past `fp_start + fp_length` returns zero bytes. For example, consider a pointer with:
```
{|
fp_start  := 0;
fp_length := 5;
fp_offset := 2
|}
```

   Reading will produce a word with 3 most significant bytes read from memory fairly (addresses 2, 3, 4) and 29 zero bytes coming from attempted reads past `fp_start + fp_length` bound.

4. Store the word to `res`.
6. Store an encoded fat pointer to the next 32-byte word in (aux_)heap in `inc_ptr`. Its fields are assigned as follows:

```
fp_page := in_ptr.(fp_page);
fp_start := in_ptr.(fp_page);
fp_length := in_ptr.(fp_length);
fp_offset := in_ptr.(fp_offset) + 32;
```   
*)
  Inductive step_load_ptr : instruction -> 
                            regs_state * memory -> Prop :=
  | step_LoadPointerInc:
    forall enc_ptr (arg_dest arg_modptr:out_reg) (arg_enc_ptr:in_reg) result new_regs new_pages addr selected_page in_ptr out_ptr slice,

      fetch arg_enc_ptr (PtrValue enc_ptr) ->
      ABI.(decode) enc_ptr = Some in_ptr ->

      validate_in_bounds in_ptr = true ->
      
      page_has_id _ old_pages in_ptr.(fp_page) (DataPage  _ selected_page) ->
      slice_from_ptr selected_page in_ptr slice ->
      
      (addr, false) = in_ptr.(fp_start) + in_ptr.(fp_offset) ->
      load_slice_result BigEndian slice addr result ->
      
      ptr_inc in_ptr out_ptr ->

      stores [
          (OutReg arg_dest,    IntValue result);
          (OutReg arg_enc_ptr, PtrValue (ABI.(encode) out_ptr))
        ] (new_regs, new_pages) ->

      step_load_ptr (OpLoadPointerInc arg_enc_ptr arg_dest arg_modptr) (new_regs, new_pages)
  .
End Defs.
