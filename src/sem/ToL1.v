From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Arith Common Ergs CallStack Event Memory isa.CoreSet State
  PrimitiveValue SemanticCommon RecordSetNotations.
Import ssreflect.tuple ssreflect.eqtype.

Section ToL1Definition.

  Open Scope ZMod_scope.
  (** # ToL1Message

## Abstract Syntax

[%OpToL1Message (in1: in_reg) (in2: in_reg) (is_first: bool)]

## Syntax

- `log.event in1, in2` aliased as `event in1, in2`
- `log.event.first in1, in2` aliased as `event.i in1, in2`

## Summary

Emit a message to L1 with provided key and value. See [%event] for more details
on events system.

## Semantic

- apply `swap` modifier.
- Fetch key and value from `key` and `value`.
- If `is_first` is `true`, mark the event as the first in a chain of events.
- Emit L1 message event.

   *)
  Inductive step_tol1: instruction -> smallstep :=

  | step_ToL1:
    forall cs new_cs is_first key value gs new_gs cost cost_truncated ts1 ts2 __ ___1,

      cost = gs_current_ergs_per_pubdata_byte gs * ergs_of L1_MESSAGE_PUBDATA_BYTES ->
      cost < (fromZ (unsigned_max ergs_bits)) ->
      cost_truncated = low ergs_bits cost ->
      pay cost_truncated cs new_cs ->

      emit_l1_msg {|
          ev_shard_id := current_shard cs;
          ev_is_first := is_first;
          ev_tx_number_in_block := gs_tx_number_in_block gs;
          ev_address := current_contract cs;
          ev_key := key;
          ev_value := value;
        |} gs new_gs ->
      ts2 = ts1 <| gs_callstack := new_cs |> ->
      step_tol1 (OpToL1Message (mk_pv __ key) (mk_pv ___1 value) is_first)
           {|
             gs_transient := ts1;
             gs_global    := gs;
           |}
           {|
             gs_transient := ts2;
             gs_global    := new_gs;
           |}
  .
(**
## Affected parts of VM state

- Event queue.

## Usage

Communicating with L1.


## Similar instructions

- [%OpSLoad], [%OpSStore], [%OpEvent], [%OpToL1Message], [%OpPrecompileCall] share the same opcode.

 *)
End ToL1Definition.
