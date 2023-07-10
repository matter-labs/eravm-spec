From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Predication Ergs CallStack Event Memory MemoryOps Instruction State ZMod
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations MetaParameters.
Import ZArith List ListNotations.

Definition current_storage_fqa (xstack:callstack) : fqa_storage :=
  mk_fqa_storage (current_shard xstack) (current_contract xstack).
Generalizable Variable __.

Inductive step: instruction -> xsmallstep :=
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
  forall flags xstack regs (arg_key: in_reg) (arg_dest_value: out_reg)
    new_regs pages read_value key (s1 s2:state) __,
    load_reg regs arg_key (mk_pv __ key) ->

    let fqa_storage := mk_fqa_key (current_storage_fqa xstack) key in

    storage_read (gs_revertable s1).(gs_depot) fqa_storage read_value ->
    store_reg regs arg_dest_value (IntValue read_value) new_regs ->
    step_xstate_only
      {|
           gs_regs         := regs;


           gs_pages        := pages;
           gs_callstack    := xstack;
           gs_flags        := flags;
         |}
         {|
           gs_regs         := new_regs;


           gs_pages        := pages;
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
