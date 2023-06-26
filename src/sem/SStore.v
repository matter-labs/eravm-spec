From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Condition Ergs CallStack Event Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations MetaParameters.
Import ZArith List ListNotations.



Inductive step: instruction -> smallstep :=
(**
# SStore

## Abstract Syntax

```
OpSStore (key: in_reg) (value: in_reg)
```

## Syntax

- `log.swrite in1, in2` aliased as `sstore in1, in2`


## Summary

Store word in current storage by key.

## Semantic

- Store word in current shard, and current contract's storage by key `key`.

  Current contract is identified by the field [ecf_this_address] of the active external frame.

- Pay for storage write.

*)
| step_SStore:
  forall flags pages xstack context_u128 regs (arg_key: in_reg) (arg_dest_value: out_reg)
    new_regs new_pages new_xstack key new_depot write_value gs new_gs,
    resolve_load_word xstack (regs,pages) arg_key key ->

    (* there are currently no refunds *)
    let fqa_storage := mk_fqa_key (current_storage_fqa xstack) key in
    let old_depot := gs.(gs_revertable).(gs_depot) in
    storage_write old_depot fqa_storage write_value new_depot ->
    global_state_new_depot new_depot gs new_gs ->


    pay (ergs_of (net_pubdata xstack)) xstack new_xstack ->
    
    resolve_store xstack (regs, pages) arg_dest_value (IntValue write_value) (new_regs, new_pages) ->
    
    step (OpSLoad arg_key arg_dest_value)
         {|
           gs_xstate := {|
           gs_regs         := regs;
           gs_pages        := pages;
           gs_callstack    := xstack;
           gs_flags        := flags;
                       |};
           gs_global       := gs;

           
           gs_context_u128 := context_u128;
         |}
         {|
           gs_xstate := {|
                         gs_regs         := new_regs;
                         gs_pages        := new_pages;
                         gs_callstack    := new_xstack;
                         gs_flags        := flags;
                       |};
           gs_global       := new_gs;

           gs_context_u128 := context_u128;
         |}
.
(**
## Affected parts of VM state

- execution stack:
  + PC, as by any instruction;
  + ergs balance
- GPRs, because `res` only resolves to a register.
- Depot of current shard.

## Usage

- Only [SStore] is capable to write data to storage.
- [SStore] is rolled back if the current frame ended by [OpPanic] or [OpRevert].

## Similar instructions

- [OpSLoad], [OpSStore], [OpEvent], [OpToL1Message], [OpPrecompileCall] share the same opcode.

 *)
