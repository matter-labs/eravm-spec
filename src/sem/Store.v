Require SemanticCommon.
Import Core Common Memory MemoryOps isa.CoreSet State ZMod
  SemanticCommon Pointer PrimitiveValue.

Section Defs.
  Open Scope ZMod_scope.

  Inductive step_store: instruction -> tsmallstep :=

  (**
# Store

## Abstract Syntax

[%OpStore (ptr: in_regimm) (val: in_reg) (mem:data_page_type)]

## Syntax

- `uma.heap_write in1, in2` aliased as `st.1 in1, out`
- `uma.aux_heap_write in1, in2` aliased as `st.2 in1, out`


## Summary

Decode the heap address from `in1`, store 32 consecutive bytes to the specified active heap variant.

## Semantic

1. Decode a [%heap_ptr] $\mathit{(addr,limit)}$ from `ptr`.

2. Ensure storing 32 consecutive bytes is possible; for that, check if $\mathit{addr < 2^{32}-32}$.

3. Let $B$ be the selected heap variant bound. If $\mathit{addr + 32} > B$, grow
   heap variant bound and pay for the growth. We are aiming at reading a 256-bit
   word starting from address $\mathit{addr}$ so the heap variant bound should
   contain all of it.
4. Store 32 consecutive bytes as a Big Endian 256-bit word from `val` to $\mathit{addr}$ in the heap variant.
5. Store an encoded [%heap_ptr] $\mathit{(addr+32, limit)}$ to the next 32-byte word in the heap variant in `inc_ptr`.

   *)

  | step_Store:
    forall flags new_cs heap_variant enc_ptr hptr value new_mem selected_page query modified_page cs regs mem __ ___ addr limit ctx,

      let selected_page_id := heap_variant_id heap_variant cs in

      hptr = mk_hptr addr limit ->

      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      heap_variant_page heap_variant cs mem selected_page ->

      word_upper_bound hptr query ->
      grow_and_pay heap_variant query cs new_cs ->

      mb_store_word_result BigEndian selected_page addr value modified_page ->

      page_replace selected_page_id (mk_page (DataPage modified_page)) mem new_mem ->

      step_store (OpStore (Some hptr, mk_pv __ enc_ptr) (mk_pv ___ value) heap_variant)
           {|
             gs_callstack    := cs;
             gs_pages        := mem;


             gs_regs         := regs;
             gs_flags        := flags;
             gs_context_u128 := ctx;
           |}
           {|
             gs_callstack    := new_cs;
             gs_pages        := new_mem;


             gs_regs         := regs;
             gs_flags        := flags;
             gs_context_u128 := ctx;
           |}

  .
(**
## Affected parts of VM state

- execution stack:

  + PC, as by any instruction;
  + ergs balance if the heap variant has to be grown;
  + heap bounds, if heap variant has to be grown.

- GPRs, because `out` only resolves to a register.
- Memory page

## Usage

- Only [%OpLoad] and [%OpLoadInc] are capable of reading data from heap variant.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc].

## Similar instructions

- [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc] are variants of the same instruction.

 *)
End Defs.
