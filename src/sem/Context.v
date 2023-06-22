From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Common Condition Ergs CallStack Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations MetaParameters.

Inductive step: instruction -> smallstep :=

| step_ContextThis:
  forall flags pages xstack regs (out_arg:out_reg) this_addr new_regs new_pages s1 s2,
    resolve_store xstack (regs,pages)
      out_arg (IntValue this_addr) (new_regs, new_pages) ->
    this_addr = resize contract_address_bits word_bits (topmost_extframe xstack).(ecf_this_address) ->

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
    step (OpContextThis out_arg) s1 s2

| step_ContextCaller:
  forall flags pages xstack regs (out_arg:out_reg) sender_addr new_regs new_pages s1 s2,
    resolve_store xstack (regs,pages)
      out_arg (IntValue sender_addr)
      (new_regs, new_pages) ->
    
    sender_addr = resize contract_address_bits word_bits (topmost_extframe xstack).(ecf_msg_sender) ->

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
    step (OpContextCaller out_arg) s1 s2
         
| step_ContextCodeAddress:
  forall flags  pages xstack regs (out:out_reg) code_addr new_regs new_pages s1 s2,
    resolve_store xstack (regs,pages)
      out (IntValue code_addr) (new_regs, new_pages) ->
    
    code_addr = resize code_address_bits word_bits (pc_get xstack) -> 
    
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
    step (OpContextCodeAddress out) s1 s2
| step_ContextErgsLeft:
  forall flags  pages xstack regs (out_arg:out_reg) balance new_regs new_pages s1 s2,
    resolve_store xstack (regs,pages)
      out_arg (IntValue balance) (new_regs, new_pages) ->
    
    balance = resize _ word_bits (topmost_extframe xstack).(ecf_common).(cf_ergs_remaining) ->
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

    step (OpContextErgsLeft out_arg) s1 s2
         
         
| step_ContextSP:
  forall flags  pages xstack regs (out_arg:out_reg) sp new_regs new_pages s1 s2,
    resolve_store xstack (regs,pages)
      out_arg (IntValue sp) (new_regs, new_pages) ->
    
    sp = resize _ word_bits (sp_get xstack) ->
    
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
    step (OpContextSp out_arg) s1 s2
         
| step_ContextGetContextU128:
  forall flags pages xstack regs (out_arg:out_reg) new_regs new_pages wcontext s1 s2,
    resolve_store xstack (regs,pages)
      out_arg (IntValue wcontext) (new_regs, new_pages) ->

    wcontext = resize _ word_bits (gs_context_u128 s1) ->  
    
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
    step (OpContextGetContextU128 out_arg) s1 s2
| step_ContextSetContextU128:
  forall gs pages xstack old_context_u128 regs (in_arg:in_reg) any_tag val new_context_u128 xstate,
    resolve_load xstack (regs,pages) in_arg (mk_pv any_tag val) ->

    new_context_u128 = resize word_bits 128 val ->
    step (OpContextSetContextU128 in_arg)
         {|
           gs_context_u128 := old_context_u128;


           gs_xstate := xstate;
           gs_global       := gs;
         |}
         {|
           gs_context_u128 := new_context_u128;

           
           gs_xstate := xstate;
           gs_global       := gs;
         |}

| step_ContextMeta:
  forall flags  pages xstack regs (out_arg:out_reg) new_regs new_pages meta_encoded
    ergs_per_pubdata s1 s2,
    resolve_store xstack (regs,pages)
      out_arg (IntValue meta_encoded) (new_regs, new_pages) ->

    let shards := (topmost_extframe xstack).(ecf_shards) in 
    meta_encoded =
      MetaParameters.ABI.(encode)
                           {|
                             ergs_per_pubdata_byte := ergs_per_pubdata;
                             heap_size := heap_bound xstack;
                             aux_heap_size := auxheap_bound xstack;
                             this_shard_id := shard_this shards;
                             caller_shard_id := shard_caller shards;
                             code_shard_id := shard_code shards;
                           |} ->
    
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
    step (OpContextMeta out_arg) s1 s2
| step_ContextIncTx:
  forall context_u128 gs new_gs xstate,
   global_state_increment_tx gs new_gs -> 
    step OpContextIncrementTxNumber
         {|
           gs_xstate       := xstate;
           
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
         {|
           gs_xstate       := xstate;
           gs_context_u128 := context_u128;
           gs_global       := new_gs;
         |}
| step_ContextSetErgsPerPubdata:
  forall gs new_gs pages context_u128 regs (in_arg:in_reg) any_tag new_val (new_val_arg:in_reg) xstate ,

    resolve_load xstate.(gs_callstack) (regs, pages) in_arg (mk_pv any_tag new_val) ->

    let new_ergs := resize _ ergs_bits new_val in
    new_gs = gs <| gs_global ::= (fun s => s <| gs_current_ergs_per_pubdata_byte := new_ergs |> ) |> ->
                                 
    step (OpContextSetErgsPerPubdataByte new_val_arg)
         {|
           gs_xstate       := xstate;
           
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
         {|
           gs_xstate       := xstate;
           gs_context_u128 := context_u128;
           gs_global       := new_gs;
         |}

.        
