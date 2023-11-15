Require SemanticCommon Slice.

Import Arith isa.CoreSet TransientMemory MemoryOps Pointer SemanticCommon PrimitiveValue Slice State.


Section LoadPtrIncDefinition.
  Open Scope ZMod_scope.

  (** # LoadPointerInc

## Abstract Syntax

[%OpLoadPointerInc  (ptr: in_reg)  (res: out_reg) (inc_ptr: out_reg)]

## Syntax

- `uma.fat_ptr_read.inc in1, out` aliased as `ld.inc in1, out`


## Summary

Read 32 consecutive bytes from address `ptr` of active `heap` or `aux_heap` page as a 256-bit word, Big Endian. Reading bytes past the slice bound yields zero bytes.

Additionally, store a pointer to the next word to `inc_ptr` register.

## Semantic

1. Let `in_ptr = (page, start, offset, length)` be a [%fat_ptr] decoded from `in1`. Requires that `in1` is tagged as a pointer.
2. Validate that offset is in bounds: `offset < length`.
3. Read 32 consecutive bytes as a Big Endian 256-bit word from address `offset` in heap variant.

   Reading bytes past `start + length` returns zero bytes. For example, consider a pointer with:

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
5. Store an encoded fat pointer to the next 32-byte word in heap variant in
   `inc_ptr`. Its fields are assigned as follows:

   ```
   page := in_ptr.(fp_page);
   start := in_ptr.(fp_page);
   length := in_ptr.(fp_length);
   offset := in_ptr.(fp_offset) + 32;
   ```
*)
  Inductive step_load_ptr_inc : instruction -> tsmallstep :=
  | step_LoadPointerInc:
    forall result addr selected_page (in_ptr:fat_ptr) out_ptr slice page_id s high128,

      validate_in_bounds in_ptr = true ->
      page_id  = in_ptr.(fp_page) ->

      page_has_id s.(gs_pages) page_id (mk_page (DataPage selected_page)) ->
      slice_page selected_page in_ptr slice ->

      ptr_resolves_to in_ptr addr ->
      mb_load_slice_result BigEndian slice addr result ->

      fat_ptr_inc in_ptr out_ptr ->

      step_load_ptr_inc (OpLoadPointerInc (Some (PtrValue (high128, NotNullPtr in_ptr))) (IntValue result) (Some (PtrValue (high128, NotNullPtr out_ptr)))) s s
  (** ## Affected parts of VM state

- execution stack: PC, as by any instruction;
- GPRs

## Usage

- Read data from a read-only slice returned from a far call, or passed to a far call.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc].

## Similar instructions

- [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc] are variants of the same instruction.

## Panics

1. Argument is not a tagged pointer. *)
  | step_LoadPointerInc_not_tagged:
    forall ___ ____ _____ (s1 s2:state),
      step_panic ExpectedFatPointer s1 s2 ->
      step_load_ptr_inc (OpLoadPointerInc (Some (IntValue ___)) ____ _____) s1 s2
(** 2. Incremented pointer overflows. *)
  | step_LoadPointerInc_inc_overflow:
    forall in_ptr high128 ____ _____ (s1 s2:state),
      fat_ptr_inc_OF in_ptr = None ->
      step_panic FatPtrIncOverflow s1 s2 ->
      step_load_ptr_inc (OpLoadPointerInc (Some (PtrValue (high128, NotNullPtr in_ptr))) ____ _____) s1 s2
.
End LoadPtrIncDefinition.
