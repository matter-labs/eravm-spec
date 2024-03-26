Require SemanticCommon MemoryManagement.
Import Core Common TransientMemory MemoryOps MemoryManagement isa.CoreSet State
  SemanticCommon Pointer PrimitiveValue.


Section StaticWriteIncDefinition.
 Open Scope ZMod_scope.

 Inductive step_static_write_inc: instruction -> tsmallstep :=
(** {{{!
describe(InstructionDoc(

ins=Instruction("OpStaticWrite", "ststi", in1 = In.RegImm, in2 = In.Reg, out1 = Out.Reg, kernelOnly = True),
legacy = """""",

summary = """
Decode the value of type [%heap_ptr] from `in1`, write 32 consecutive bytes from `in2` to the static memory page.

Additionally, write an incremented [%heap_ptr] value to `out1`.
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

  | step_StaticWriteInc:
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

      step_static_write_inc (OpStaticWriteInc (Some (IntValue (high224, hptr))) (mk_pv ___1 value) (Some (IntValue (high224,hptr_mod))))
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
    forall ___1 ___2 addr s1 s2 high224,
      `(
          addr > MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
          step_panic HeapPtrOffsetTooLarge s1 s2 ->
          step_static_write_inc (OpStaticWriteInc (Some (IntValue (high224, mk_hptr addr))) ___1 ___2) s1 s2
        )
  (** 2. Fat pointer provided where heap pointer is expected. *)
  | step_StaticWrite_expects_intvalue:
    forall s1 s2 ___1 ___2 ___3,
      `(
          step_panic ExpectedHeapPointer  s1 s2 ->
          step_static_write_inc (OpStaticWriteInc (Some (PtrValue ___1)) ___2 ___3 ) s1 s2
        )
  (** 3. Incrementing the pointer leads to overflow. *)
  | step_StaticWrite_inc_overflow:
    forall (s1 s2:state) hptr ___1 ___2 high242,
      `(
          hp_inc_OF hptr = None ->
          step_panic HeapGrowthUnaffordable s1 s2 ->
          step_static_write_inc (OpStaticWriteInc (Some (IntValue (high242, hptr))) ___1 ___2 ) s1 s2
        )
  (** Working with static memory page never leads to memory growth. *)
       .
End StaticWriteIncDefinition.
