Require SemanticCommon MemoryManagement.
Import Core Common Memory MemoryOps MemoryManagement  isa.CoreSet State
  SemanticCommon Pointer PrimitiveValue.

Section StoreDefinition.
  Open Scope ZMod_scope.

  Inductive step_store: instruction -> tsmallstep :=

    (** # Store

## Abstract Syntax

[% OpStore    (ptr: in_regimm) (val: in_reg)  (mem:data_page_type) (swap: mod_swap)]

## Syntax

- `uma.heap_write in1, in2` aliased as `st.1.inc in1, out`
- `uma.aux_heap_write in1, in2` aliased as `st.2.inc in1, out`


## Summary

Decode the heap address from `in1`, load 32 consecutive bytes from the specified active heap variant.

## Semantic

1. Apply `swap` modifier.
2. Decode a [%heap_ptr] $\mathit{addr}$ from `ptr`.

2. Ensure storing 32 consecutive bytes is possible; for that, check if $\mathit{addr < 2^{32}-32}$.

3. Let $B$ be the selected heap variant bound. If $\mathit{addr + 32} > B$, grow
   heap variant bound and pay for the growth. We are aiming at reading a 256-bit
   word starting from address $\mathit{addr}$ so the heap variant bound should
   contain all of it.
4. Store 32 consecutive bytes as a Big Endian 256-bit word from `val` to
   $\mathit{addr}$ in the heap variant.
*)
  | step_Store:
    forall flags new_cs heap_variant enc_ptr hptr value new_mem selected_page bound modified_page cs regs mem __ ___1 addr ctx,

      let selected_page_id := heap_variant_id heap_variant cs in

      hptr = mk_hptr addr ->

      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      heap_variant_page heap_variant cs mem selected_page ->

      word_upper_bound hptr bound ->
      bound_grow_pay (heap_variant, bound) cs new_cs ->

      mb_store_word_result BigEndian selected_page addr value modified_page ->

      page_replace selected_page_id (mk_page (DataPage modified_page)) mem new_mem ->

      step_store (OpStore (Some hptr, mk_pv __ enc_ptr) (mk_pv ___1 value) heap_variant)
           {|
             gs_callstack    := cs;
             gs_pages        := mem;


             gs_regs         := regs;
             gs_flags        := flags;
             gs_context_u128 := ctx;
             gs_status       := NoPanic;
           |}
           {|
             gs_callstack    := new_cs;
             gs_pages        := new_mem;


             gs_regs         := regs;
             gs_flags        := flags;
             gs_context_u128 := ctx;
             gs_status       := NoPanic;
           |}

(** ## Affected parts of VM state

- execution stack:

  + PC, as by any instruction;
  + allocated ergs if the heap variant has to be grown;
  + heap bounds, if heap variant has to be grown.

- GPRs, because `out` only resolves to a register.
- Memory page

## Usage

- Only [%OpLoad] and [%OpLoadInc] are capable of reading data from heap variant.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc].

## Similar instructions

- [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc] are variants of the same instruction.

## Panic

1. Accessing an address greater than [%MAX_OFFSET_TO_DEREF_LOW_U32].
 *)
  | step_Store_offset_too_large:
    forall heap_variant __ ___1 addr s1 s2,
      `(
          addr > MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
          step_panic HeapPtrOffsetTooLarge s1 s2 ->
          step_store (OpStore (Some (mk_hptr addr), __) ___1 heap_variant) s1 s2
        )
  (** 2. Trying to store a word from an address greater than
   [%MAX_OFFSET_TO_DEREF_LOW_U32]. *)
  | step_Store_expects_intvalue:
    forall s1 s2 __ ___1 ___2 ___3,
      `(
          step_panic ExpectedHeapPointer  s1 s2 ->
          step_store (OpStore (Some __, PtrValue ___1) ___2 ___3) s1 s2
        )
  (** 3. Accessing an address requires growing the bound of the
       corresponding heap variant, but the growth is unaffordable. *)
  | step_Store_growth_unaffordable:
    forall (s1 s2:state) cs ptr bound heap_variant __ ___1,
      `(
          word_upper_bound ptr bound ->
          growth_to_bound_unaffordable cs (heap_variant, bound) ->
          gs_callstack s1 = cs ->
          step_panic HeapGrowthUnaffordable s1 s2 ->
          step_store (OpStore (Some ptr, __) ___1 heap_variant) s1 s2
        )
  .
End StoreDefinition.
