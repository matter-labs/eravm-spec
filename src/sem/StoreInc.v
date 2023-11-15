Require SemanticCommon MemoryManagement.
Import Core Common TransientMemory MemoryOps MemoryManagement isa.CoreSet State
  SemanticCommon Pointer PrimitiveValue.


Section StoreIncDefinition.
 Open Scope ZMod_scope.

 Inductive step_storeinc: instruction -> tsmallstep :=
(**
# StoreInc

## Abstract Syntax

[% OpStoreInc    (ptr: in_regimm) (val: in_reg)  (mem:data_page_type) (inc_ptr: out_reg) (swap: mod_swap)]

## Syntax

- `uma.inc.heap_write in1, in2` aliased as `st.1.inc in1, out`
- `uma.inc.aux_heap_write in1, in2` aliased as `st.2.inc in1, out`


## Summary

Decode the heap address from `in1`, load 32 consecutive bytes from the specified active heap variant.
Additionally, store a pointer to the next word to `inc_ptr` register.

## Semantic

1. Decode a [%heap_ptr] $\mathit{addr}$ from `ptr`.

2. Ensure storing 32 consecutive bytes is possible; for that, check if $\mathit{addr < 2^{32}-32}$.

3. Let $B$ be the selected heap variant bound. If $\mathit{addr + 32} > B$, grow
   heap variant bound and pay for the growth. We are aiming at reading a 256-bit
   word starting from address $\mathit{addr}$ so the heap variant bound should
   contain all of it.
4. Store 32 consecutive bytes as a Big Endian 256-bit word from `val` to
   $\mathit{addr}$ in the heap variant.
5. Store an encoded [%heap_ptr] $\mathit{addr+32}$ to the next 32-byte
   word in the heap variant in `inc_ptr`.
*)
  | step_StoreInc:
    forall hptr flags new_cs heap_variant value new_mem selected_page bound modified_page cs regs mem ___1 addr hptr_mod ctx high224,

      let selected_page_id := heap_variant_id heap_variant cs in

      hptr = mk_hptr addr ->

      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      heap_variant_page heap_variant cs mem selected_page ->

      word_upper_bound hptr bound ->
      bound_grow_pay (heap_variant, bound) cs new_cs ->

      mb_store_word_result BigEndian selected_page addr value modified_page ->
      page_replace selected_page_id (mk_page (DataPage modified_page)) mem new_mem ->

      hp_inc hptr hptr_mod ->

      step_storeinc (OpStoreInc (Some (IntValue (high224, hptr))) (mk_pv ___1 value) heap_variant (Some (IntValue (high224,hptr_mod))))
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
  + heap variant bounds, if heap variant has to be grown.

- GPRs, because `res` and `inc_ptr` only resolve to registers.

## Usage

- Only [%OpStore] and [%OpStoreInc] are capable of writing to heap variant.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc].

## Similar instructions

- [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc] are variants of the same instruction.

## Panics

1. Accessing an address greater than [%MAX_OFFSET_TO_DEREF_LOW_U32].
 *)
  | step_Store_offset_too_large:
    forall heap_variant ___1 ___2 addr s1 s2 high224,
      `(
          addr > MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
          step_panic HeapPtrOffsetTooLarge s1 s2 ->
          step_storeinc (OpStoreInc (Some (IntValue (high224, mk_hptr addr))) ___1 heap_variant ___2) s1 s2
        )
  (** 2. Fat pointer provided where heap pointer is expected. *)
  | step_Store_expects_intvalue:
    forall s1 s2 ___1 ___2 ___3 ___4,
      `(
          step_panic ExpectedHeapPointer  s1 s2 ->
          step_storeinc (OpStoreInc (Some (PtrValue ___1)) ___2 ___3 ___4) s1 s2
        )
  (** 3. Accessing an address requires growing the bound of the
       corresponding heap variant, but the growth is unaffordable. *)
  | step_Store_growth_unaffordable:
    forall (s1 s2:state) cs hptr bound heap_variant ___1 ___2 high242,
      `(
          word_upper_bound hptr bound ->
          growth_to_bound_unaffordable cs (heap_variant, bound) ->
          gs_callstack s1 = cs ->
          step_panic HeapGrowthUnaffordable s1 s2 ->
          step_storeinc (OpStoreInc (Some (IntValue (high242, hptr))) ___1 heap_variant ___2) s1 s2
        )
  (** 4. Incrementing the pointer leads to overflow. *)
  | step_Store_inc_overflow:
    forall (s1 s2:state) hptr ___1 ___2 ___3 high242,
      `(
          hp_inc_OF hptr = None ->
          step_panic HeapGrowthUnaffordable s1 s2 ->
          step_storeinc (OpStoreInc (Some (IntValue (high242, hptr))) ___1 ___2 ___3) s1 s2
        )
       .
End StoreIncDefinition.
