From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Condition Ergs CallStack Event Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations MetaParameters.
Import ZArith List ListNotations.


Inductive step_precompile: instruction -> smallstep :=
| step_PrecompileCall_unaffordable:
  forall flags pages xstack regs (arg_params arg_extra_ergs: in_reg) (arg_dest: out_reg) 
    new_regs new_pages params extra_ergs s1 s2,
    
    resolve_load_words xstack (regs, pages) [
        (InReg arg_params, params);
        (InReg arg_extra_ergs, extra_ergs)
      ] ->

    let cost := resize _ ergs_bits extra_ergs in
    affordable xstack cost = false ->

    resolve_store xstack (regs,pages)
                  arg_dest (IntValue zero256)
                  (new_regs, new_pages) ->
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
        gs_callstack    := ergs_reset xstack;
        
        gs_flags        := flags;
      |} s1 s2 -> 
    step_precompile (OpPrecompileCall arg_params arg_extra_ergs) s1 s2
                    
| step_PrecompileCall_affordable:
  forall flags pages xstack regs (arg_params arg_extra_ergs: in_reg) (arg_dest: out_reg)
    regs1 xstack1 pages1 ext_params new_regs new_pages new_xstack enc_params extra_ergs gs new_gs context_u128,
    let heap_id := active_heap_id xstack in
    
    resolve_load_words xstack (regs, pages) [
        (InReg arg_params, enc_params);
        (InReg arg_extra_ergs, extra_ergs)
      ] ->

    let cost := resize _ ergs_bits extra_ergs in

    pay cost xstack xstack1 ->
    resolve_store xstack1 (regs,pages)
                  arg_dest (IntValue one256)
                  (regs1, pages1) ->

    PrecompileParameters.pub_ABI.(decode) enc_params = Some ext_params ->
    let in_params := PrecompileParameters.to_inner heap_id heap_id ext_params in

    let new_xs := {|
        gs_regs         := new_regs;
        gs_pages        := new_pages;
        gs_callstack    := new_xstack;
        
        gs_flags        := flags;
      |} in
    precompile_processor (current_contract xstack) in_params 
    {|
        gs_regs         := regs1;
        gs_pages        := pages1;
        gs_callstack    := xstack1;
        
        gs_flags        := flags;
    |} new_xs ->
    
   emit_event (PrecompileQuery {|
                   q_contract_address := current_contract xstack;
                   q_tx_number_in_block := gs_tx_number_in_block gs;
                   q_shard_id := current_shard xstack;
                   q_key := in_params;
                 |}) gs new_gs ->
    step_precompile (OpPrecompileCall arg_params arg_extra_ergs) {|
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
           gs_xstate       := new_xs;
           gs_global       := new_gs;

           gs_context_u128 := context_u128;
         |}
.
