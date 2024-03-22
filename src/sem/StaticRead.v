Require SemanticCommon MemoryManagement.

Import Arith MemoryOps MemoryManagement isa.CoreSet Pointer SemanticCommon PrimitiveValue State.

Section StaticReadDefinition.

  Open Scope ZMod_scope.

  Generalizable Variables cs flags regs mem.
  Inductive step_static_read: instruction -> tsmallstep :=
  (** # StaticRead
## Abstract Syntax

[%OpStaticRead (ptr: in_regimm) (res: out_reg)]

## Legacy Syntax

None.

## Syntax

`ldsti in1, out `

## Summary

Kernel-only.

TODO

## Semantic

FIXME semantic is incorrect.
   *)
  | step_StaticRead:
    forall new_cs ctx result mem selected_page bound addr high224,
      `(
          addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

          mb_load_result BigEndian selected_page addr result ->

          word_upper_bound (mk_hptr addr) bound ->

          step_static_read (OpStaticRead (Some (IntValue (high224, mk_hptr addr))) (IntValue result))
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
  (** ## Affected parts of VM state

- execution stack:

  + PC, as by any instruction;
  + ergs allocated for the current function/contract instance, if the heap
    variant has to be grown;
- static memory page
- registers, because `res` only resolves to a register.

## Usage

TODO

## Similar instructions

TODO

## Panics

1. Accessing an address greater than [%MAX_OFFSET_TO_DEREF_LOW_U32].
   *)
  | step_StaticRead_offset_too_large:
    forall ___ addr s1 s2 high224,
      `(
          addr > MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
          step_panic HeapPtrOffsetTooLarge s1 s2 ->
          step_static_read (OpStaticRead (Some (IntValue (high224, mk_hptr addr))) ___ ) s1 s2
        )
  (** 2. Passed [%fat_ptr] instead of [%heap_ptr]. *)
  | step_StaticRead_expects_intvalue:
    forall s1 s2  ___ ____,
      `(
          step_panic ExpectedHeapPointer s1 s2 ->
          step_static_read (OpStaticRead (Some (PtrValue ___)) ____) s1 s2
        )
  (** Working with static memory page never leads to memory growth. *)
  .
End StaticReadDefinition.
