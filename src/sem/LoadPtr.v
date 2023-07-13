Require SemanticCommon Addressing Slice.

Import ABI Addressing Common Coder CallStack GPR Pointer  Memory MemoryOps Instruction ZMod
  Addressing.Coercions SemanticCommon MemoryContext Pointer PrimitiveValue State Slice.

Import FatPointer.
Import List ListNotations.
Import Addressing.Coercions.


Section Defs.

  Open Scope ZMod_scope.
  Inductive step_load_ptr : instruction -> xsmallstep :=

 (**
# LoadPointer


## Abstract Syntax

[%OpLoadPointer (ptr: in_reg)  (res: out_reg)]

## Syntax

- `uma.fat_ptr_read in1, out` aliased as `ld in1, out`


## Summary

Read 32 consecutive bytes from address `ptr` of active `heap` or `aux_heap` page as a 256-bit word, Big Endian. Reading bytes past the slice bound yields zero bytes.

## Semantic

1. Decode a [%fat_ptr] `in_ptr` from `ptr`.

2. Validate that offset is in bounds: `offset < length`.

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
*)
  | step_LoadPointer:
    forall enc_ptr (arg_dest: out_reg) (arg_enc_ptr: in_reg) result regs new_regs mem addr selected_page in_ptr slice cs flags page_id,

      load_reg regs arg_enc_ptr (PtrValue enc_ptr) ->

      decode_fat_ptr enc_ptr = Some in_ptr ->

      validate_in_bounds in_ptr = true ->
      Some page_id  =in_ptr.(fp_page) ->
      page_has_id mem page_id (@DataPage era_pages selected_page) ->
      slice_page selected_page in_ptr slice ->

      ptr_resolves_to in_ptr addr  ->
      mb_load_slice_result BigEndian slice addr result ->

      store_reg regs arg_dest (IntValue result) new_regs ->

      step_load_ptr (OpLoadPointer arg_enc_ptr arg_dest)
        (mk_exec_state flags regs mem cs)
        (mk_exec_state flags new_regs mem cs)
  .

(**
## Affected parts of VM state

- execution stack: PC, as by any instruction;
- GPRs, because `res` only resolves to a register.

## Usage

- Read data from a read-only slice returned from a far call, or passed to a far call.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc].

## Similar instructions

- [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc] are variants of the same instruction.

 *)
End Defs.
