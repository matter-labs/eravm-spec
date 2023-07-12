From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Predication Ergs CallStack Event Memory MemoryOps Instruction State ZMod
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations MetaParameters.
Import ZArith List ListNotations.

Section ToL1.

  Open Scope ZMod_scope.
(**
# ToL1Message

## Abstract Syntax

[%OpToL1Message (key: in_reg) (value: in_reg) (is_first: bool)]

## Syntax

- `log.event in1, in2` aliased as `event in1, in2`
- `log.event.first in1, in2` aliased as `event.i in1, in2`

## Summary

Emit a message to L1 with provided key and value. See [%event] for more details on events system.

## Semantic

- Fetch key and value from `key` and `value`.
- If `is_first` is `true`, mark the event as the first in a chain of events.
- Emit L1 message event.

 *)
Inductive step: instruction -> smallstep :=

| step_ToL1:
  forall flags cs new_cs context_u128 regs (arg_key: in_reg) (arg_value: in_reg) is_first
    pages key value gs new_gs cost __ ___,
    load_regs regs [
        (arg_key, mk_pv __ key);
        (arg_value, mk_pv ___ value)
      ] ->

    (cost, false) = gs_current_ergs_per_pubdata_byte gs * ergs_of L1_MESSAGE_PUBDATA_BYTES ->
    pay cost cs new_cs ->

    emit_l1_msg {|
        ev_shard_id := current_shard cs;
        ev_is_first := is_first;
        ev_tx_number_in_block := gs_tx_number_in_block gs;
        ev_address := current_contract cs;
        ev_key := key;
        ev_value := value;
      |} gs new_gs ->

    step (OpToL1Message arg_key arg_value is_first)
         {|
           gs_xstate := {|
                         gs_callstack    := cs;

                         gs_regs         := regs;
                         gs_pages        := pages;
                         gs_flags        := flags;
                         |};

           gs_global       := gs;
           gs_context_u128 := context_u128;
         |}
         {|
           gs_xstate := {|
                         gs_callstack    := new_cs;

                         gs_regs         := regs;
                         gs_pages        := pages;
                         gs_flags        := flags;
                       |};

           gs_global       := new_gs;
           gs_context_u128 := context_u128;
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
End ToL1.
