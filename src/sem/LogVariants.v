From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Condition Ergs CallStack Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations MetaParameters.
Import ZArith.

Definition is_rollup (xstack: callstack) : bool := zero8 == current_shard xstack.

Inductive step: instruction -> smallstep :=

| step_SLoad:
  forall gs flags pages xstack context_u128 regs (arg_key: in_reg) (arg_dest_value: out_reg)
    new_regs new_pages read_value key,
    resolve_fetch_word regs xstack pages arg_key key ->
      
    storage_read gs.(gs_revertable).(gs_depot) (mk_fqa_key (current_shard xstack) (current_contract xstack) key) read_value ->
    resolve_store xstack (regs, pages) arg_dest_value (IntValue read_value) (new_regs, new_pages) ->
    step (OpSLoad arg_key arg_dest_value)
         {|
           gs_regs         := regs;
           gs_pages        := pages;
           gs_callstack    := xstack;
           gs_flags        := flags;
           
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;


           gs_callstack    := xstack;
           gs_flags        := flags;
           
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}.
