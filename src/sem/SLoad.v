Require SemanticCommon.
Import  isa.CoreSet TransientMemory memory.Depot PrimitiveValue SemanticCommon State.

Section SLoadDefinition.
  Generalizable Variable __.

  Inductive step_sload: instruction -> smallstep :=
(**
{{{!describe(InstructionDoc(

ins=Instruction(abstract_name  = "OpSLoad", mnemonic = "lds", in1= In.Reg, out1 = Out.Reg),

legacy=" `log.sread in1, out` aliased as `sload in1, out` ",

summary = """
Access word in the storage of the active contract by key.
""",
semantic = r"""
1. Load word from current shard, current contract's storage by key `key`.

   Current contract is identified by the field [%ecf_this_address] of the active
   external frame.
2. Store the value to `dest`.
""",
usage = """
- Only [%OpSLoad] is capable of reading data from transient storage.
"""
))
}}}
   *)

  | step_SLoad:
    forall read_value key (s:state) __,
      let fqa_storage := mk_fqa_key (current_storage_fqa (gs_callstack s)) key in

      storage_read (gs_revertable s).(gs_depot) fqa_storage read_value ->
      step_sload (OpSLoad (mk_pv __ key)(IntValue read_value)) s s
  .
End SLoadDefinition.
