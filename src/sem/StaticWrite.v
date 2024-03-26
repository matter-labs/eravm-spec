Require SemanticCommon MemoryManagement.
Import Core Common TransientMemory MemoryOps MemoryManagement  isa.CoreSet State
  SemanticCommon Pointer PrimitiveValue.

Section StaticWriteDefinition.
  Open Scope ZMod_scope.

  Inductive step_static_write: instruction -> tsmallstep :=

    (** {{{!
describe(InstructionDoc(

ins=Instruction("OpStaticWrite", "stst", in1 = In.RegImm, in2 = In.Reg, kernelOnly = True),
legacy = """""",

summary = """
Decode the value of type [%heap_ptr] from `in1`, write 32 consecutive bytes from `in2` to the static memory page.
""",

semantic = r"""
TODO
""",

usage = """
""",

similar = f"""
- Only [%OpStaticWrite] and [%OpStaticWriteInc] are capable of writing data to the static memory page.
- {USES_REGIMM}
""",

affectedState = """
- static memory page
"""
))
}}} *)
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

(** ## Panics

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
