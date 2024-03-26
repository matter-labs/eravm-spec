Require SemanticCommon MemoryManagement.

Import Arith MemoryOps MemoryManagement isa.CoreSet Pointer SemanticCommon PrimitiveValue State.

Section StaticReadIncDefinition.

  Open Scope ZMod_scope.
  Generalizable Variables cs flags regs mem.
  Inductive step_static_read_inc : instruction -> tsmallstep :=

    (** {{{!
describe(InstructionDoc(

ins=Instruction("OpStaticReadInc", "ldsti", in1 = In.RegImm, out1=Out.Reg, out2=Out.Reg, kernelOnly = True),
legacy = """""",

summary = """
Decode the value of [%heap_ptr] type from `in1`, load 32 consecutive bytes from static memory page.

Additionally, increment this pointer by 32 and write it to `out2`.
""",

semantic = r"""
TODO
""",
usage = """
""",

similar = f"""
- Only [%OpStaticRead] and [%OpStaticReadInc] are capable of reading data from the static memory page.
- {USES_REGIMM}
""",

affectedState = """
- static memory page
"""
))
}}} *)
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
  (** ## Panics

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
