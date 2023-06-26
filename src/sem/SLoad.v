From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Condition Ergs CallStack Event Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations MetaParameters.
Import ZArith List ListNotations.

Definition is_rollup (xstack: callstack) : bool := zero8 == current_shard xstack.

Definition net_pubdata xstack : Z := if is_rollup xstack then INITIAL_STORAGE_WRITE_PUBDATA_BYTES else 0.
    
Definition current_storage_fqa (xstack:callstack) : fqa_storage :=
  mk_fqa_storage (current_shard xstack) (current_contract xstack).


Inductive step: instruction -> smallstep :=
(**
# SLoad


## Abstract Syntax

```
OpSLoad (key: in_reg) (dest: out_reg)
```

## Syntax

- `log.sread in1, out` aliased as `sload in1, out`


## Summary

Access word in current storage by key.

## Semantic

1. Load word from current shard, current contract's storage by key `key`.

   Current contract is identified by the field [ecf_this_address] of the active external frame.
2. Store the value to `dest`.

*)
| step_SLoad:
  forall flags pages xstack regs (arg_key: in_reg) (arg_dest_value: out_reg)
    new_regs new_pages read_value key (s1 s2:state),
    resolve_load_word xstack (regs,pages) arg_key key ->

    let fqa_storage := mk_fqa_key (current_storage_fqa xstack) key in
     
    storage_read (gs_revertable s1).(gs_depot) fqa_storage read_value ->
    resolve_store xstack (regs, pages) arg_dest_value (IntValue read_value) (new_regs, new_pages) ->
    step_xstate
      {|
           gs_regs         := regs;
           gs_pages        := pages;
           gs_callstack    := xstack;
           gs_flags        := flags;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;

           gs_callstack    := xstack;
           gs_flags        := flags;
           
         |} s1 s2 ->
    step (OpSLoad arg_key arg_dest_value) s1 s2
.
(**
## Affected parts of VM state

- execution stack: PC, as by any instruction;
- GPRs, because `res` only resolves to a register.

## Usage

- Only [SLoad] is capable of reading data from storage.

## Similar instructions

- [OpSLoad], [OpSStore], [OpEvent], [OpToL1Message], [OpPrecompileCall] share the same opcode.

 *)
