From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Coder Core Common Predication Ergs CallStack TransientMemory MemoryOps isa.CoreSet State
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations ABI.MetaParametersABI.

Section VMDefinitions.

  Inductive step_vm: instruction -> smallstep :=
  (**
{{{! describe(InstructionDoc(

ins=Instruction(abstract_name  = "OpVMErgsLeft", mnemonic = "ergs",out1= Out.Reg),

legacy = "`context.ergs_left out`",

summary = """
Retrieves the number of ergs allocated for the current frame.
""",
semantic = r"""
- Fetch the currently allocated ergs from the topmost frame, external or internal.
  The `ergs` belonging to the parent frames are not counted.
- Widen the ergs number to [%word_bits], zero-extended, and write to `out`.
""",

usage = """
- Check if the number of ergs is sufficient for an expensive task.
- Should be used before [%OpPrecompileCall].
""",

))
}}}
*)
  | step_VMErgsLeft:
    forall ergs_left_word (s1 s2:state),
      ergs_left_word = widen word_bits (ergs_remaining (gs_callstack s1)) ->
      step_vm (OpVMErgsLeft (IntValue ergs_left_word)) s1 s2

  (** {{{! describe(InstructionDoc(

ins=Instruction(abstract_name  = "OpVMSP", mnemonic = "sp", out1 = Out.Reg),

legacy = "`context.sp out`",

summary = """
Retrieves current stack pointer value.
""",
semantic = r"""
- Fetch the current SP from the topmost frame, external or internal. It points past the topmost element of the stack.
- Widen the SP value to [%word_bits], zero-extended, and write to `out`.
""",

usage = """
""",

similar = """
"""
))
}}}
   *)
  | step_VMSP:
    forall sp_zero_padded (s1 s2 :state),
      sp_zero_padded = widen word_bits (sp_get (gs_callstack s1)) ->

      step_vm (OpVMSP (IntValue sp_zero_padded)) s1 s2

  (** {{{! describe(InstructionDoc(

ins=Instruction(abstract_name  = "OpVMMeta", mnemonic = "meta", out1= Out.Reg),

legacy = """
```
context.meta  out
```
""",

summary = """
VM internal state introspection.
""",
semantic = r"""
- Stores the encoded value of [%MetaParametersABI] in `out`. The value is structured as follows:

```
Record params := {
      ergs_per_pubdata_byte: ergs;
      heap_size: mem_address;
      aux_heap_size: mem_address;
      this_shard_id: shard_id;
      caller_shard_id: shard_id;
      code_shard_id: shard_id;
    }.
```
""",
usage = """
""",
))
}}}
   *)
  | step_VMMeta:
    forall params cs shards
      (s1 s2: state),
      cs = gs_callstack s1 ->
      shards = (active_extframe cs).(ecf_shards) ->
      params = {|
                 ergs_per_pubdata_byte := gs_current_ergs_per_pubdata_byte s1;
                 heap_size := heap_bound cs;
                 aux_heap_size := auxheap_bound cs;
                 this_shard_id := shard_this shards;
                 caller_shard_id := shard_caller shards;
                 code_shard_id := shard_code shards;
               |} ->
      step_vm (OpVMMeta (Some (IntValue params))) s1 s2
  .
End VMDefinitions.
