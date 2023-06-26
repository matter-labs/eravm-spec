From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Condition Ergs CallStack Event Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations MetaParameters.
Import ZArith List ListNotations.



Inductive step: instruction -> smallstep :=
| step_Event:
  forall flags pages xstack context_u128 regs (arg_key: in_reg) (arg_value: in_reg) is_first
    new_regs new_pages key value gs new_gs,
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
                         
                         gs_callstack    := xstack;
                         gs_flags        := flags;
                       |};
           
           gs_global       := new_gs;


           gs_context_u128 := context_u128;
         |}.
