Require SemanticCommon MemoryManagement.
Import Core Common TransientMemory MemoryOps MemoryManagement  isa.CoreSet State
  SemanticCommon Pointer PrimitiveValue.

Section StaticWriteDefinition.
  Open Scope ZMod_scope.

  Inductive step_static_write: instruction -> tsmallstep :=

    (** # StaticWrite

## Abstract Syntax

[%OpStaticWrite (ptr: in_regimm) (val: in_reg)]


## Syntax

`stst in1, in2`

## Legacy Syntax

None


## Summary

TODO

## Semantic

FIXME

*)
  | step_StaticWrite:
    forall high224 result flags new_cs value new_mem selected_page bound modified_page cs regs mem addr ctx,

      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

      word_upper_bound (mk_hptr addr) bound ->

      mb_store_word_result BigEndian selected_page addr value modified_page ->


      step_static_write (OpStaticWrite (Some (IntValue (high224, mk_hptr addr))) (IntValue result))
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
  + static memory page

- GPRs, because `out` only resolves to a register.
- TransientMemory page

## Usage

TODO

## Similar instructions

TODO

## Panics

1. Accessing an address greater than [%MAX_OFFSET_TO_DEREF_LOW_U32].
 *)
  | step_StaticWrite_offset_too_large:
    forall  ___1 addr high224 s1 s2,
      `(
          addr > MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
          step_panic HeapPtrOffsetTooLarge s1 s2 ->
          step_static_write (OpStaticWrite (Some (IntValue (high224, mk_hptr addr))) ___1) s1 s2
        )
  (** 2. Fat pointer provided where heap pointer is expected. *)
  | step_StaticWrite_expects_intvalue:
    forall s1 s2 ___1 ___2,
      `(
          step_panic ExpectedHeapPointer  s1 s2 ->
          step_static_write (OpStaticWrite (Some (PtrValue ___1)) ___2) s1 s2
        )
  (** Working with static memory page never leads to memory growth. *)
  .
End StaticWriteDefinition.
