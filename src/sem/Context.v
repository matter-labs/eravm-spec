From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Condition ExecutionStack Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations MetaParameters.

Inductive step: instruction -> smallstep :=

| step_ContextThis:
  forall codes flags depot pages xstack context_u128 regs (out_arg:out_reg) this_addr new_regs new_pages,
    resolve_store regs xstack pages
      out_arg (IntValue this_addr) (new_regs, new_pages) ->
    this_addr = resize contract_address_bits word_bits (topmost_extframe xstack).(ecf_this_address) ->
    
    step (OpContextThis out_arg)
         {|
           gs_regs         := regs;
           gs_pages        := pages;
           
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;


           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
| step_ContextCaller:
  forall codes flags depot pages xstack context_u128 regs (out_arg:out_reg) sender_addr new_regs new_pages,
    resolve_store regs xstack pages
      out_arg (IntValue sender_addr)
      (new_regs, new_pages) ->
    sender_addr = resize contract_address_bits word_bits (topmost_extframe xstack).(ecf_msg_sender) ->
    
    step (OpContextCaller out_arg)
         {|
           gs_regs         := regs;
           gs_pages        := pages;
           
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;


           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
| step_ContextCodeAddress:
  forall codes flags depot pages xstack context_u128 regs (out:out_reg) code_addr new_regs new_pages,
    resolve_store regs xstack pages
      out (IntValue code_addr) (new_regs, new_pages) ->
    
    code_addr = resize code_address_bits word_bits (pc_get xstack) -> 
    
    step (OpContextCaller out)
         {|
           gs_regs         := regs;
           gs_pages        := pages;
           
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;


           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
| step_ContextErgsLeft:
  forall codes flags depot pages xstack context_u128 regs (out_arg:out_reg) balance new_regs new_pages,
    resolve_store regs xstack pages
      out_arg (IntValue balance) (new_regs, new_pages) ->
    
    balance = resize _ word_bits (topmost_extframe xstack).(ecf_common).(cf_ergs_remaining) ->
    
    step (OpContextErgsLeft out_arg)
         {|
           gs_regs         := regs;
           gs_pages        := pages;
           
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;


           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         
| step_ContextSP:
  forall codes flags depot pages xstack context_u128 regs (out_arg:out_reg) sp new_regs new_pages,
    resolve_store regs xstack pages
      out_arg (IntValue sp) (new_regs, new_pages) ->
    
    sp = resize _ word_bits (sp_get xstack) ->
    
    step (OpContextSp out_arg)
         {|
           gs_regs         := regs;
           gs_pages        := pages;
           
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;


           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         
| step_ContextGetContextU128:
  forall codes flags depot pages xstack context_u128 regs (out_arg:out_reg) new_regs new_pages wcontext,
    resolve_store regs xstack pages
      out_arg (IntValue wcontext) (new_regs, new_pages) ->

    wcontext = resize _ word_bits context_u128 ->  
    
    step (OpContextGetContextU128 out_arg)
         {|
           gs_regs         := regs;
           gs_pages        := pages;

           
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;

           
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         
| step_ContextSetContextU128:
  forall codes flags depot pages xstack old_context_u128 regs (in_arg:in_reg) any_tag val new_context_u128,
    resolve_fetch_value regs xstack pages
      in_arg (mk_pv any_tag val) ->

    new_context_u128 = resize word_bits 128 val ->
    step (OpContextSetContextU128 in_arg)
         {|
           gs_context_u128 := old_context_u128;

           
           gs_regs         := regs;
           gs_pages        := pages;
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_contracts    := codes;
         |}
         {|
           gs_context_u128 := new_context_u128;

           
           gs_regs         := regs;
           gs_pages        := pages;
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_contracts    := codes;
         |}

(* Fixme: shards, tx are not implemented *)
| step_ContextMeta:
  forall codes flags depot pages xstack context_u128 regs (out_arg:out_reg) new_regs new_pages meta_encoded
    ergs_per_pubdata
    shard_id
    caller_shard
    code_shard,
    resolve_store regs xstack pages
      out_arg (IntValue meta_encoded) (new_regs, new_pages) ->

    meta_encoded =
      MetaParameters.ABI.(encode)
                           {|
                             ergs_per_pubdata_byte := ergs_per_pubdata;
                             heap_size := heap_bound xstack;
                             aux_heap_size := auxheap_bound xstack;
                             this_shard_id := shard_id;
                             caller_shard_id := caller_shard;
                             code_shard_id := code_shard;
                           |} ->
    
    step (OpContextMeta out_arg)
         {|
           gs_regs         := regs;
           gs_pages        := pages;

           
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;

           
           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
.
