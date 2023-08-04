Require SemanticCommon.

Import MemoryOps isa.CoreSet Pointer SemanticCommon PrimitiveValue State ZMod.

Section Defs.

  Open Scope ZMod_scope.

  Generalizable Variables cs flags regs mem.
  Inductive step_load: instruction -> tsmallstep :=
  (**
# Load


## Abstract Syntax

[%OpLoad (ptr: in_regimm) (res: out_reg) (mem:data_page_type)]

## Syntax

- `uma.heap_read in1, out` aliased as `ld.1 in1, out`
- `uma.aux_heap_read in1, out` aliased as `ld.2 in1, out`


## Summary

Decode the heap address from `in1`, load 32 consecutive bytes from the specified active heap variant.

## Semantic

1. Decode a [%heap_ptr] $\mathit{(addr,limit)}$ from `ptr`.

2. Ensure reading 32 consecutive bytes is possible; for that, check if $\mathit{addr < 2^{32}-32}$.

3. Let $B$ be the selected heap variant bound. If $\mathit{addr + 32} > B$, grow
   heap variant bound and pay for the growth. We are aiming at reading a 256-bit
   word starting from address $\mathit{addr}$ so the heap variant bound should
   contain all of it.
4. Read 32 consecutive bytes as a Big Endian 256-bit word from $\mathit{addr}$ in the heap variant, store result to `res`.
*)
  | step_Load:
    forall new_cs heap_variant ctx result __ mem selected_page query addr limit,
      `(
      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      heap_variant_page heap_variant cs1 mem selected_page ->
      mb_load_result BigEndian selected_page addr result ->

      word_upper_bound (mk_hptr addr limit) query ->
      grow_and_pay heap_variant query cs1 new_cs ->

      step_load (OpLoad (Some (mk_hptr addr limit), __) (IntValue result) heap_variant)
         {|
           gs_callstack    := cs0;


           gs_regs         := regs;
           gs_pages        := mem;
           gs_flags        := flags;
           gs_context_u128 := ctx;
         |}
         {|
           gs_callstack    := new_cs;


           gs_regs         := regs;
           gs_pages        := mem;
           gs_flags        := flags;
           gs_context_u128 := ctx;
         |}
        )
  .
(**
## Affected parts of VM state

- execution stack:

  + PC, as by any instruction;
  + ergs balance if the heap variant has to be grown;
  + heap variant bounds, if heap variant has to be grown.

- GPRs, because `res` only resolves to a register.

## Usage

- Only [%OpLoad] and [%OpLoadInc] are capable of reading data from heap/aux_heap.
- One of few instructions that accept only reg or imm operand but do not have full addressing mode, therefore can't e.g. address stack. The full list is: [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc].

## Similar instructions

- [%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc] are variants of the same instruction.

 *)
End Defs.
