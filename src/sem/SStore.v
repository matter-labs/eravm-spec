From RecordUpdate Require Import RecordSet.
Require SemanticCommon.

Import Common Core Predication Ergs isa.CoreSet CallStack Event memory.Depot TransientMemory MemoryOps State
  PrimitiveValue SemanticCommon ZArith RecordSetNotations.

Section SStoreDefinition.

  Definition sstore_cost cs : ergs :=
    let pubdata :=  (net_pubdata cs) in
    ergs_of (pubdata * Z.of_nat bytes_in_word).

  Inductive step_sstore: instruction -> smallstep :=
  (** # SStore

## Abstract Syntax

[%OpSStore (in1: in_reg) (in2: in_reg)]

## Syntax

- `log.swrite in1, in2` aliased as `sstore in1, in2`

## Summary

Store word in current storage by key.

## Semantic

- Store word in current shard, and current contract's storage by key `key`.

  Current contract is identified by the field [%ecf_this_address] of the active external frame.

- Pay for storage write.

   *)
  | step_SStore:
    forall cs new_cs key new_depot write_value gs new_gs ts1 ts2 __ ,

      (* there are currently no refunds *)
      cs = gs_callstack ts1 ->
      let fqa_storage := mk_fqa_key (current_storage_fqa cs) key in
      let old_depot := gs.(gs_revertable).(gs_depot) in
      storage_write old_depot fqa_storage write_value new_depot ->
      global_state_new_depot new_depot gs new_gs ->

      ts2 = ts1 <| gs_callstack := new_cs |> ->
      pay (sstore_cost cs) cs new_cs ->

      step_sstore (OpSStore (mk_pv __ key) (IntValue write_value))
                  {|
                    gs_transient := ts1;
                    gs_global    := gs;
                  |}
                  {|
                    gs_transient := ts2;
                    gs_global    := new_gs;
                  |}
(** ## Affected parts of VM state

- execution stack:
  + PC, as by any instruction;
  + allocated ergs
- GPRs, because `res` only resolves to a register.
- Depot of current shard.

## Usage

- Only [%SStore] is capable to write data to storage.
- [%SStore] is rolled back if the current frame ended by [%OpPanic] or [%OpRevert].

## Similar instructions

- [%OpSLoad], [%OpSStore], [%OpEvent], [%OpToL1Message], [%OpPrecompileCall] share the same opcode.

## Panics

1. Not enough ergs to pay for storage write.
 *)
  | step_SStore_unaffordable:
    forall cs gs ts1 ts2 ___1 ___2,

      (* there are currently no refunds *)
      cs = gs_callstack ts1 ->
      affordable cs (sstore_cost cs) = false ->
      ts2 = ts1 <| gs_status := Panic StorageWriteUnaffordable |> ->
      step_sstore (OpSLoad ___1 ___2)
                  {|
                    gs_transient := ts1;
                    gs_global    := gs;
                  |}
                  {|
                    gs_transient := ts2;
                    gs_global    := gs;
                  |}
.
End SStoreDefinition.
