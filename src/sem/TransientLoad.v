Require SemanticCommon.
Import  isa.CoreSet TransientMemory memory.Depot PrimitiveValue SemanticCommon State.

Section TransientLoadDefinition.
  Generalizable Variable __.

  Inductive step_tload: instruction -> smallstep :=
  (** # TransientLoad

## Abstract Syntax

[%OpTransientLoad (key: in_reg) (dest: out_reg)]

## Syntax

- `ldt in1, out`

## Legacy Syntax

- `tload in1, out`

## Summary

Access word in current transient storage by key.
Transient contract storage of all contracts resets when [%OpIncrementTxNumber] is called.

## Semantic

1. Load word from current shard, current contract's transient storage by key `key`.

   Current contract is identified by the field [%ecf_this_address] of the active
   external frame.
2. Store the value to `dest`.

   *)

  (* FIXME: semantic is incorrect *)
  | step_TLoad:
    forall read_value key (s:state) __,
      let fqa_storage := mk_fqa_key (current_storage_fqa (gs_callstack s)) key in

      storage_read (gs_revertable s).(gs_depot) fqa_storage read_value ->
      step_tload (OpSLoad (mk_pv __ key)(IntValue read_value)) s s
  .
(** ## Affected parts of VM state

- execution stack: PC, as by any instruction;
- GPRs, because `res` only resolves to a register.
- transient storage of current contract.

## Usage

- Only [%TLoad] is capable of reading data from transient storage.

## Similar instructions

- [%OpSLoad], [%OpSStore], [%OpEvent], [%OpToL1Message], [%OpPrecompileCall],
  [%OpTransientLoad], [%OpTransientStore] share the same opcode.
*)
End TransientLoadDefinition.
