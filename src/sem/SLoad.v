Require SemanticCommon.
Import  isa.CoreSet Memory PrimitiveValue SemanticCommon State.

Section SLoadDefinition.
  Generalizable Variable __.

  Inductive step_sload: instruction -> smallstep :=
  (** # SLoad

## Abstract Syntax

[%OpSLoad (key: in_reg) (dest: out_reg)]

## Syntax

- `log.sread in1, out` aliased as `sload in1, out`

## Summary

Access word in current storage by key.

## Semantic

1. Load word from current shard, current contract's storage by key `key`.

   Current contract is identified by the field [%ecf_this_address] of the active
   external frame.
2. Store the value to `dest`.

   *)
  | step_SLoad:
    forall read_value key (s:state) __,
      let fqa_storage := mk_fqa_key (current_storage_fqa (gs_callstack s)) key in

      storage_read (gs_revertable s).(gs_depot) fqa_storage read_value ->
      step_sload (OpSLoad (mk_pv __ key)(IntValue read_value)) s s
  .
(** ## Affected parts of VM state

- execution stack: PC, as by any instruction;
- GPRs, because `res` only resolves to a register.

## Usage

- Only [%SLoad] is capable of reading data from storage.

## Similar instructions

- [%OpSLoad], [%OpSStore], [%OpEvent], [%OpToL1Message], [%OpPrecompileCall] share the same opcode.
*)
End SLoadDefinition.
