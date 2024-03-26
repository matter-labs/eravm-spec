Require SemanticCommon Slice.

Import TransientMemory MemoryOps isa.CoreSet Pointer SemanticCommon PrimitiveValue Slice State.

Section LoadPtrDefinition.

  Open Scope ZMod_scope.
  Inductive step_load_ptr : instruction -> tsmallstep :=

 (** {{{!
describe(InstructionDoc(

ins=Instruction("OpLoadPtr", "ldp", in1 = In.RegImm, out1=Out.Reg),
legacy = """
- `uma.fat_ptr_read in1, out` aliased as `ld in1, out`
""",

summary = """
Read 32 consecutive bytes from address provided by a fat pointer `ptr` of active `heap` or `aux_heap` page
as a 256-bit word, Big Endian. Reading bytes past the slice bound yields zero
bytes.
""",

semantic = r"""
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
""",

usage = """
- Read data from a read-only slice returned from a far call, or passed to a far call.
- One of few instructions that accept only reg or imm operand but do not have
  full addressing mode, therefore can't e.g. address stack. The full list is: {INSNS_USE_REGIMM}.
""",

similar = """
See [%OpLoadPtrInc].
""",

affectedState = """
- execution stack:
  + ergs allocated for the current function/contract instance, if the heap
    variant has to be grown;
  + heap variant bounds, if heap variant has to be grown.
"""
))
}}}
*)
  | step_LoadPointer:
    forall result _flags _regs mem _cs _ctx addr selected_page (in_ptr:fat_ptr) slice page_id high128,
      validate_in_bounds in_ptr = true ->
      page_id = in_ptr.(fp_page) ->
      page_has_id mem page_id (mk_page (DataPage selected_page)) ->
      slice_page selected_page in_ptr slice ->

      ptr_resolves_to in_ptr addr  ->
      mb_load_slice_result BigEndian slice addr result ->

      step_load_ptr (OpLoadPointer (Some (PtrValue (high128, NotNullPtr in_ptr))) (IntValue result))
                    (mk_transient_state _flags _regs mem _cs _ctx NoPanic)
                    (mk_transient_state _flags _regs mem _cs _ctx NoPanic)
(** ## Panics

1. Argument is not a tagged pointer. *)
  | step_LoadPointer_not_tagged:
    forall ___ ____ (s1 s2:state),
      step_panic ExpectedFatPointer s1 s2 ->
      step_load_ptr (OpLoadPointer (Some (IntValue ___)) ____) s1 s2
  .
End LoadPtrDefinition.
