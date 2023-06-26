Require SemanticCommon.

Import Addressing Common CallStack Event MemoryOps Instruction State 
  Addressing.Coercions SemanticCommon .
Import List ListNotations.

Inductive step: instruction -> smallstep :=
(**
# Event

## Abstract Syntax

```
OpEvent (key: in_reg) (value: in_reg) (is_first: bool)
```

## Syntax

- `log.event in1, in2` aliased as `event in1, in2`
- `log.event.first in1, in2` aliased as `event.i in1, in2`

## Summary

Emit an event with provided key and value. See [event] for more details on events system.

## Semantic

- Fetch key and value from `key` and `value`.
- If `is_first` is `true`, mark the event as the first in a chain of events. 
- Emit event. 

 *)
| step_Event:
  forall context_u128 xs (arg_key: in_reg) (arg_value: in_reg) is_first
    key value gs new_gs,
    let regs := gs_regs xs in
    let pages := gs_pages xs in
    let xstack := gs_callstack xs in
    resolve_load_words xstack (regs, pages) [
        (InReg arg_key, key);
        (InReg arg_value, value)
      ] ->

    emit_event (EventQuery {|
                    ev_shard_id := current_shard xstack;
                    ev_is_first := is_first;
                    ev_tx_number_in_block := gs_tx_number_in_block gs;
                    ev_address := current_contract xstack;
                    ev_key := key;
                    ev_value := value;
                  |}) gs new_gs ->
    
    
    step (OpEvent arg_key arg_value is_first)
         {|
           gs_global       := gs;

           gs_xstate       := xs;
           gs_context_u128 := context_u128;
         |}
         {|
           gs_global       := new_gs;


           gs_xstate       := xs;
           gs_context_u128 := context_u128;
         |}.
(**
## Affected parts of VM state

- Event queue.

## Usage TODO 


## Similar instructions

- [OpSLoad], [OpSStore], [OpEvent], [OpToL1Message], [OpPrecompileCall] share the same opcode.

 *)
