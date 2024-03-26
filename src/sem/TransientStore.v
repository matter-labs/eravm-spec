From RecordUpdate Require Import RecordSet.
Require SemanticCommon.

Import Common Core Predication Ergs isa.CoreSet CallStack Event memory.Depot TransientMemory MemoryOps State
  PrimitiveValue SemanticCommon ZArith RecordSetNotations.

Section TransientStoreDefinition.

  Definition tstore_cost cs : ergs :=
    let pubdata :=  (net_pubdata cs) in
    ergs_of (pubdata * Z.of_nat bytes_in_word).

  Inductive step_tstore: instruction -> smallstep :=
  (** {{{!
describe(InstructionDoc(

ins=Instruction(abstract_name  = "OpTransientStore", mnemonic = "stt", in1= In.Reg, in2 = In.Reg),

legacy="`tstore in1, in2`",

summary = """
Store word in the transient storage of the active contract by key.
""",
semantic = r"""
- Store word in current shard's, and current contract's transient storage by key `key`.
  Current contract is identified by the field [%ecf_this_address] of the active external frame.
- Pay for transient storage write.
""",

usage = """
- Only [%OpTransientStore] is capable to write data to storage.
- [%OpTransientStore] is rolled back if the current frame ended by [%OpPanic] or [%OpRevert].
- Transient storage is reset after the transaction ends.
""",
affectedState =
"- Transient depot of the current shard."

))
}}}

   *)
  (* FIXME: semantic is incorrect *)
  | step_TransientStore:
    forall cs new_cs key new_depot write_value gs new_gs ts1 ts2 __ ,

      (* there are currently no refunds *)
      cs = gs_callstack ts1 ->
      let fqa_storage := mk_fqa_key (current_storage_fqa cs) key in
      let old_depot := gs.(gs_revertable).(gs_depot) in
      storage_write old_depot fqa_storage write_value new_depot ->
      global_state_new_depot new_depot gs new_gs ->

      ts2 = ts1 <| gs_callstack := new_cs |> ->
      pay (tstore_cost cs) cs new_cs ->

      step_tstore (OpTransientStore (mk_pv __ key) (IntValue write_value))
                  {|
                    gs_transient := ts1;
                    gs_global    := gs;
                  |}
                  {|
                    gs_transient := ts2;
                    gs_global    := new_gs;
                  |}
(**

## Panics

1. Not enough ergs to pay for storage write.
 *)

  (* FIXME: semantic *)
  | step_TransientStore_unaffordable:
    forall cs gs ts1 ts2 ___1 ___2,

      (* there are currently no refunds *)
      cs = gs_callstack ts1 ->
      affordable cs (tstore_cost cs) = false ->
      ts2 = ts1 <| gs_status := Panic StorageWriteUnaffordable |> ->
      step_tstore (OpSLoad ___1 ___2)
                  {|
                    gs_transient := ts1;
                    gs_global    := gs;
                  |}
                  {|
                    gs_transient := ts2;
                    gs_global    := gs;
                  |}
.
End TransientStoreDefinition.
