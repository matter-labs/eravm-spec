Require SemanticCommon MemoryManagement.

Import Arith MemoryOps MemoryManagement isa.CoreSet Pointer SemanticCommon PrimitiveValue State.

Section StaticReadIncDefinition.

  Open Scope ZMod_scope.
  Generalizable Variables cs flags regs mem.
  Inductive step_static_read_inc : instruction -> tsmallstep :=
  (** # StaticReadInc

## Abstract Syntax

[%OpStaticReadInc (ptr: in_regimm) (res: out_reg) (inc_ptr: out_reg)]

## Syntax

`ldsti in1, out1, out2`

## Legacy Syntax

None


## Summary

Kernel-only.

TODO

## Semantic

FIXME incorrect semantic

   *)
  | step_StaticReadInc:
    forall result new_regs selected_page high224 ptr_inc bound new_cs addr ctx,
      `(
          let hptr := mk_hptr addr in

          addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->

          mb_load_result BigEndian selected_page addr result ->

          word_upper_bound hptr bound ->

          hp_inc hptr ptr_inc ->

          step_static_read_inc (OpStaticReadInc (Some (IntValue (high224, hptr))) (IntValue result) (Some (IntValue (high224, ptr_inc))))
            (mk_transient_state flags regs mem cs0 ctx NoPanic)
            (mk_transient_state flags new_regs mem new_cs ctx NoPanic)
        )
  (** ## Affected parts of VM state

TODO

## Usage

TODO

## Similar instructions

TODO

## Panics

1. Accessing an address greater than [%MAX_OFFSET_TO_DEREF_LOW_U32].
   *)
  | step_StaticRead_offset_too_large:
    forall ___ ____ addr s1 s2 high224,
      `(
          addr > MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
          step_panic HeapPtrOffsetTooLarge s1 s2 ->
          step_static_read_inc (OpStaticReadInc (Some (IntValue (high224, mk_hptr addr))) ___ ____) s1 s2
        )
  (** 2. Passed [%fat_ptr] instead of [%heap_ptr]. *)
  | step_StaticRead_expects_intvalue:
    forall s1 s2 ___ ____ _____,
      `(
          step_panic ExpectedHeapPointer s1 s2 ->
          step_static_read_inc (OpStaticReadInc (Some (PtrValue ___)) ____ _____) s1 s2
        )
  (** 3. Incremented pointer overflows. *)
  | step_StaticReadInc_inc_overflow:
    forall (s1 s2:state) result hptr ___ high224,
      `(
          hp_inc_OF hptr = None ->
          step_panic HeapPtrIncOverflow s1 s2 ->
          step_static_read_inc (OpStaticReadInc (Some (IntValue (high224, hptr))) (IntValue result) ___) s1 s2
        )
  (** Working with static memory page never leads to memory growth. *)
  .

End StaticReadIncDefinition.
