Require SemanticCommon MemoryManagement.

Import Arith MemoryOps MemoryManagement isa.CoreSet Pointer SemanticCommon PrimitiveValue State.

Section StaticReadDefinition.

  Open Scope ZMod_scope.

  Generalizable Variables cs flags regs mem.
  Inductive step_static_read: instruction -> tsmallstep :=
  (** {{{!
describe(InstructionDoc(

ins=Instruction("OpStaticRead", "ldst", in1 = In.RegImm, out1=Out.Reg, kernelOnly = True),
legacy = """""",

summary = """
Decode the value of [%heap_ptr] type from `in1`, load 32 consecutive bytes from static memory page.
""",

semantic = r"""
TODO
""",

usage = """
- Only [%OpStaticRead] and [%OpStaticReadInc] are capable of reading data from static memory page.
- {USES_REGIMM}
""",

similar = """
""",

affectedState = """
- static memory page
"""
))
}}} *)
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
  (** ## Panics

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
