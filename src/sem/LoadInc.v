Require SemanticCommon.

Import MemoryOps isa.CoreSet Pointer SemanticCommon PrimitiveValue State ZMod.

Section LoadIncDefinition.

  Open Scope ZMod_scope.
  Generalizable Variables cs flags regs mem.
  Inductive step_load_inc : instruction -> tsmallstep :=
  (** # LoadInc

## Abstract Syntax

[%OpLoadInc (ptr: in_regimm) (res: out_reg) (mem:data_page_type) (inc_ptr: out_reg)]

## Syntax

- `uma.inc.heap_read in1, out1, out2` aliased as `ld.1.inc in1, out1, out2`
- `uma.inc.aux_heap_read in1, out1, out2` aliased as `ld.2.inc in1, out1, out2`

## Summary

Decode the heap address from `in1`, load 32 consecutive bytes from the specified
active heap variant.
Additionally, store a pointer to the next word to `inc_ptr` register.

## Semantic

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
*)
  | step_LoadInc:
    forall heap_variant result new_regs selected_page ptr_inc query new_cs addr src_tag __ ___ ctx,
      `(
      let hptr := mk_hptr addr in

      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      heap_variant_page heap_variant cs0 mem selected_page ->
      mb_load_result BigEndian selected_page addr result ->

      word_upper_bound hptr query ->
      grow_and_pay heap_variant query cs0 new_cs ->

      hp_inc hptr ptr_inc ->

      step_load_inc (OpLoadInc (Some hptr, mk_pv src_tag __) (IntValue result) heap_variant (ptr_inc, mk_pv src_tag ___))
        (mk_transient_state flags regs mem cs0 ctx)
        (mk_transient_state flags new_regs mem new_cs ctx)
        )
  .
(**
## Affected parts of VM state

- execution stack:

  + PC, as by any instruction;
  + allocated ergs if the heap variant has to be grown;
  + heap variant bounds, if heap variant has to be grown.

- GPRs, because `res` and `inc_ptr` only resolve to registers.

## Usage

- Only [%OpLoad] and [%OpLoadInc] are capable of reading from heap variantheap.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc].

## Similar instructions

- [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc] are variants of the same instruction.

 *)

End LoadIncDefinition.
