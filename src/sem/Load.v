Require SemanticCommon MemoryManagement.

Import Arith MemoryOps MemoryManagement isa.CoreSet Pointer SemanticCommon PrimitiveValue State.

Section LoadDefinition.

  Open Scope ZMod_scope.

  Generalizable Variables cs flags regs mem.
  Inductive step_load: instruction -> tsmallstep :=
  (**

{{{!
describe(InstructionDoc(

ins=Instruction("OpLoad", "ldvl", in1 = In.RegImm, out1=Out.Reg, modifiers = [Modifier.DataPageType]),
legacy = """
- `uma.heap_read in1, out` aliased as `ld.1 in1, out`
- `uma.aux_heap_read in1, out` aliased as `ld.2 in1, out`
""",

summary = """
Decode the heap address from `in1`, load 32 consecutive bytes from the specified
active heap variant.
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
""",

usage = """
- Only [%OpLoad] and [%OpLoadInc] are capable of reading data from heap variants.
- One of few instructions that accept only reg or imm operand but do not have
  full addressing mode, therefore can't e.g. address stack. The full list is:
  [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer],
  [%OpLoadPointerInc].
""",

similar = """
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
  | step_Load:
    forall new_cs heap_variant ctx result mem selected_page bound addr high224,
      `(
      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      heap_variant_page heap_variant cs1 mem selected_page ->
      mb_load_result BigEndian selected_page addr result ->

      word_upper_bound (mk_hptr addr) bound ->
      bound_grow_pay (heap_variant, bound) cs0 new_cs ->

      step_load (OpLoad (Some (IntValue (high224, mk_hptr addr))) (IntValue result) heap_variant)
         {|
           gs_callstack    := cs0;


           gs_regs         := regs;
           gs_pages        := mem;
           gs_flags        := flags;
           gs_context_u128 := ctx;
          gs_status       := NoPanic;
         |}
         {|
           gs_callstack    := new_cs;


           gs_regs         := regs;
           gs_pages        := mem;
           gs_flags        := flags;
           gs_context_u128 := ctx;
          gs_status       := NoPanic;
         |}
        )
(**

## Panics

1. Accessing an address greater than [%MAX_OFFSET_TO_DEREF_LOW_U32].
 *)
  | step_Load_offset_too_large:
    forall heap_variant ___ addr s1 s2 high224,
      `(
          addr > MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
          step_panic HeapPtrOffsetTooLarge s1 s2 ->
          step_load (OpLoad (Some (IntValue (high224, mk_hptr addr))) ___ heap_variant) s1 s2
        )
  (** 2. Passed [%fat_ptr] instead of [%heap_ptr]. *)
  | step_Load_expects_intvalue:
    forall s1 s2  ___ ____ _____,
      `(
          step_panic ExpectedHeapPointer s1 s2 ->
          step_load (OpLoad (Some (PtrValue ___)) ____ _____) s1 s2
        )
  (** 3. Accessing an address requires growing the bound of the
       corresponding heap variant, but the growth is unaffordable. *)
  | step_Load_growth_unaffordable:
    forall (s1 s2:state) cs ptr bound heap_variant ___ high224,
      `(
          word_upper_bound ptr bound ->
          growth_to_bound_unaffordable cs (heap_variant, bound) ->
          gs_callstack s1 = cs ->
          step_panic HeapGrowthUnaffordable s1 s2 ->
          step_load (OpLoad (Some (IntValue (high224, ptr ))) ___ heap_variant) s1 s2
        )
  .
End LoadDefinition.
