Require SemanticCommon MemoryManagement.

Import Arith MemoryOps MemoryManagement isa.CoreSet Pointer SemanticCommon PrimitiveValue State.

Section LoadIncDefinition.

  Open Scope ZMod_scope.
  Generalizable Variables cs flags regs mem.
  Inductive step_load_inc : instruction -> tsmallstep :=
(** {{{
ins=Instruction("OpLoadInc", "ldvli", in1 = In.RegImm, out1=Out.Reg, out2=Out.Reg, modifiers = [Modifier.DataPageType])
descr = InstructionDoc(ins=ins,
legacy = """
- `uma.inc.heap_read in1, out1, out2` aliased as `ld.1.inc in1, out1, out2`
- `uma.inc.aux_heap_read in1, out1, out2` aliased as `ld.2.inc in1, out1, out2`
""",
syntax_override = heap_var_op_syntax(ins),

summary = """
Decode the heap address from `in1`, load 32 consecutive bytes from the specified
active heap variant.
Additionally, store a pointer to the next word to `inc_ptr` register.
""",

semantic = r"""
1. Decode a [%heap_ptr] $\mathit{addr}$ from `ptr`.

2. Ensure reading 32 consecutive bytes is possible; for that, check if
   $\mathit{addr < 2^{32}-32}$.

3. Let $B$ be the selected heap variant bound. If $\mathit{addr + 32} > B$, grow
   heap variant bound and pay for the growth. We are aiming at reading a 256-bit
   word starting from address $\mathit{addr}$ so the heap variant bound should
   contain all of it.
4. Read 32 consecutive bytes as a Big Endian 256-bit word from $\mathit{addr}$
   in the heap variant, store result to `res`.

5. Store an encoded [%heap_ptr] $\mathit{addr+32}$ to the next 32-byte
   word in the heap variant in `inc_ptr`.
""",

usage = f"""
- Only [%OpLoad] and [%OpLoadInc] are capable of reading data from heap variants.
- {USES_REGIMM}
""",

similar = f"""
See {INSNS_WORKING_WITH_HEAPS}.
""",

affectedState = """
- execution stack:
  + ergs allocated for the current function/contract instance, if the heap
    variant has to be grown;
  + heap variant bounds, if heap variant has to be grown.
"""
)
describe(descr)
}}}

*)
  | step_LoadInc:
    forall heap_variant result new_regs selected_page high224 ptr_inc bound new_cs addr ctx,
      `(
      let hptr := mk_hptr addr in

      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      heap_variant_page heap_variant cs0 mem selected_page ->
      mb_load_result BigEndian selected_page addr result ->

      word_upper_bound hptr bound ->
      bound_grow_pay (heap_variant, bound) cs0 new_cs ->

      hp_inc hptr ptr_inc ->

      step_load_inc (OpLoadInc (Some (IntValue (high224, hptr))) (IntValue result) heap_variant (Some (IntValue (high224, ptr_inc))))
        (mk_transient_state flags regs mem cs0 ctx NoPanic)
        (mk_transient_state flags new_regs mem new_cs ctx NoPanic)
        )

(** ## Panics

1. Accessing an address greater than [%MAX_OFFSET_TO_DEREF_LOW_U32].
 *)
  | step_Load_offset_too_large:
    forall heap_variant ___ ____ addr s1 s2 high224,
      `(
          addr > MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
          step_panic HeapPtrOffsetTooLarge s1 s2 ->
          step_load_inc (OpLoadInc (Some (IntValue (high224, mk_hptr addr))) ___ heap_variant ____) s1 s2
        )
  (** 2. Passed [%fat_ptr] instead of [%heap_ptr]. *)
  | step_Load_expects_intvalue:
    forall s1 s2 ___ ____ _____ ______,
      `(
          step_panic ExpectedHeapPointer s1 s2 ->
          step_load_inc (OpLoadInc (Some (PtrValue ___)) ____ _____ ______) s1 s2
        )
  (** 3. Accessing an address requires growing the bound of the
       corresponding heap variant, but the growth is unaffordable. *)
  | step_Load_growth_unaffordable:
    forall (s1 s2:state) cs ptr bound heap_variant ___ ____ high224,
      `(
          word_upper_bound ptr bound ->
          growth_to_bound_unaffordable cs (heap_variant, bound) ->
          gs_callstack s1 = cs ->
          step_panic HeapGrowthUnaffordable s1 s2 ->
          step_load_inc (OpLoadInc (Some (IntValue (high224, ptr))) ___ heap_variant ____) s1 s2
        )
  (** 4. Incremented pointer overflows. *)
  | step_LoadInc_inc_overflow:
    forall (s1 s2:state) heap_variant result hptr ___ high224,
      `(
          hp_inc_OF hptr = None ->
          step_panic HeapPtrIncOverflow s1 s2 ->
          step_load_inc (OpLoadInc (Some (IntValue (high224, hptr))) (IntValue result) heap_variant ___) s1 s2
        )
  .

End LoadIncDefinition.
