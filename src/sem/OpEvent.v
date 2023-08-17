Require SemanticCommon.

Import CallStack Event isa.CoreSet State PrimitiveValue SemanticCommon.

Inductive step_event: instruction -> smallstep :=
(**
# Event

## Abstract Syntax

[%OpEvent (in1: in_reg) (in2: in_reg) (is_first: bool) (swap:mod_swap)]

## Syntax

- `log.event in1, in2` aliased as `event in1, in2`
- `log.event.first in1, in2` aliased as `event.i in1, in2`

## Summary

Emit an event with provided key and value. See [%event] for more details on
events system.

## Semantic

- Apply `swap` modifier.
- Fetch key and value from `in1` and `in2`.
- If `is_first` is `true`, mark the event as the first in a chain of events.
- Emit event.

 *)
| step_Event:
  forall xs is_first __ ___
    key value gs new_gs,
    let regs := gs_regs xs in
    let pages := gs_pages xs in
    let xstack := gs_callstack xs in

    emit_event (EventQuery {|
                    ev_shard_id := current_shard xstack;
                    ev_is_first := is_first;
                    ev_tx_number_in_block := gs_tx_number_in_block gs;
                    ev_address := current_contract xstack;
                    ev_key := key;
                    ev_value := value;
                  |}) gs new_gs ->

    step_event (OpEvent (mk_pv __ key) (mk_pv ___ value) is_first)
         {|
           gs_global       := gs;
           gs_transient    := xs;
         |}
         {|
           gs_global       := new_gs;
           gs_transient    := xs;
         |}.
(**
## Affected parts of VM state

- Event queue.

## Usage TODO


## Similar instructions

- [%OpSLoad], [%OpSStore], [%OpEvent], [%OpToL1Message], [%OpPrecompileCall] are variants of the same [%mach_instruction].

 *)
