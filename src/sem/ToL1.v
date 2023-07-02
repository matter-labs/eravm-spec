From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Condition Ergs CallStack Event Memory MemoryOps Instruction State ZMod
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations MetaParameters.
Import ZArith List ListNotations.

Section Def.

  Open Scope ZMod_scope.

Inductive step: instruction -> smallstep :=

| step_ToL1:
  forall flags pages xstack new_xstack context_u128 regs (arg_key: in_reg) (arg_value: in_reg) is_first 
    new_regs new_pages key value gs new_gs cost __ ___,
    load_regs regs [
        (arg_key, mk_pv __ key);
        (arg_value, mk_pv ___ value)
      ] ->

    (cost, false) = gs_current_ergs_per_pubdata_byte gs * ergs_of L1_MESSAGE_PUBDATA_BYTES ->
    pay cost xstack new_xstack ->

    emit_l1_msg {|
        ev_shard_id := current_shard xstack;
        ev_is_first := is_first;
        ev_tx_number_in_block := gs_tx_number_in_block gs;
        ev_address := current_contract xstack;
        ev_key := key;
        ev_value := value;
      |} gs new_gs ->
    
    step (OpToL1Message arg_key arg_value is_first)
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
End Def.
