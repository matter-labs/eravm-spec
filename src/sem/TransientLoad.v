Require SemanticCommon.
Import  isa.CoreSet TransientMemory memory.Depot PrimitiveValue SemanticCommon State.

Section TransientLoadDefinition.
  Generalizable Variable __.

  Inductive step_tload: instruction -> smallstep :=
(**
{{{!describe(InstructionDoc(

ins=Instruction(abstract_name  = "OpTransientLoad", mnemonic = "ldt", in1= In.Reg, out1 = Out.Reg),

legacy="`tload in1, out1`",

summary = """
Access word in the transient storage of the active contract by key.

Transient contract storage of all contracts resets when [%OpIncrementTxNumber] is called.
""",
semantic = r"""
1. Load word from current shard, current contract's transient storage by key `key`.

   Current contract is identified by the field [%ecf_this_address] of the active
   external frame.
2. Store the value to `dest`.
""",
usage = """
- Only [%OpTransientLoad] is capable of reading data from transient storage.
- Much cheaper than storage for e.g. reentrancy locks.
"""
))
}}}
   *)

  (* FIXME: semantic is incorrect *)
  | step_TLoad:
    forall read_value key (s:state) __,
      let fqa_storage := mk_fqa_key (current_storage_fqa (gs_callstack s)) key in

      storage_read (gs_revertable s).(gs_depot) fqa_storage read_value ->
      step_tload (OpSLoad (mk_pv __ key)(IntValue read_value)) s s
  .

End TransientLoadDefinition.
