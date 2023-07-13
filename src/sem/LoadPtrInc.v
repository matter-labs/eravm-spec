Require SemanticCommon Addressing Slice.


Import ABI Addressing Common Coder Predication CallStack Memory MemoryOps Instruction 
  Addressing.Coercions SemanticCommon MemoryContext PrimitiveValue Pointer State Slice ZMod.

Import FatPointer.
Import List ListNotations.


Section Defs.
  Import Pointer.Coercions.
  Open Scope ZMod_scope.

  (**
# LoadPointerInc


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

1. Decode a [%fat_ptr] `in_ptr` from `ptr`.

2. Validate that offset is in bounds: `fp_offset < fp_length`.

3. Read 32 consecutive bytes as a Big Endian 256-bit word from address `fp_offset` in heap variant.

   Reading bytes past `fp_start + fp_length` returns zero bytes. For example, consider a pointer with:
```
{|
page   := _;
start  := 0;
length := 5;
offset := 2
|}
```

   Reading will produce a word with 3 most significant bytes read from memory fairly (addresses 2, 3, 4) and 29 zero bytes coming from attempted reads past `fp_start + fp_length` bound.

4. Store the word to `res`.
6. Store an encoded fat pointer to the next 32-byte word in heap variant in `inc_ptr`. Its fields are assigned as follows:

```
fp_page := in_ptr.(fp_page);
fp_start := in_ptr.(fp_page);
fp_length := in_ptr.(fp_length);
fp_offset := in_ptr.(fp_offset) + 32;
```
*)
  Inductive step_load_ptr : instruction -> xsmallstep :=
  | step_LoadPointerInc:
    forall flags regs enc_ptr (arg_dest arg_modptr:out_reg) (arg_enc_ptr:in_reg) result cs new_regs mem addr selected_page in_ptr out_ptr slice page_id,

      load_reg regs arg_enc_ptr (PtrValue enc_ptr) ->

      decode_fat_ptr enc_ptr = Some in_ptr ->

      validate_in_bounds in_ptr = true ->

      Some page_id  = in_ptr.(fp_page) ->

      page_has_id mem page_id (@DataPage era_pages selected_page) ->
      slice_page selected_page in_ptr slice ->

      ptr_resolves_to in_ptr addr ->
      mb_load_slice_result BigEndian slice addr result ->

      fp_inc in_ptr out_ptr ->

      store_regs regs [
          (arg_dest,    IntValue result);
          (arg_enc_ptr, PtrValue (encode_fat_ptr out_ptr))
        ] new_regs ->

      step_load_ptr (OpLoadPointerInc arg_enc_ptr arg_dest arg_modptr)
        (mk_exec_state flags regs mem cs)
        (mk_exec_state flags new_regs mem cs)
  .
End Defs.
