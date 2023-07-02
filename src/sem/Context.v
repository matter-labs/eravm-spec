From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Coder Core Common Condition Ergs CallStack Memory MemoryOps Instruction State ZMod
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations ABI.MetaParameters.

(**  

# ContextThis

## Abstract Syntax

[OpContextThis (out: out_reg)]

## Syntax

```
context.self_address out
```

## Summary

Retrieves the address of the currently executed contract.


## Semantic

- Fetch the address of the currently executed contract
from the active external frame.
- Widen the address to [word_bits], zero-extended, and write to register `out`.


## Affected parts of VM state

- registers : `out` register is modified.

## Usage

On delegatecall this address is preserved to be one of the caller.
See [FarCall.select_this_address].

## Similar instructions

See [OpContextCaller], [OpContextCodeAddress].

## Encoding

- Shares opcode with other `contextX` instructions.

 *)
Inductive step: instruction -> smallstep :=

| step_ContextThis:
  forall flags mem cs regs (out_arg:out_reg) this_addr new_regs s1 s2,

    store_reg regs out_arg (IntValue this_addr) new_regs ->
    
    this_addr = resize contract_address_bits word_bits (topmost_extframe cs).(ecf_this_address) ->

    
    step_xstate_only
      {|
        gs_regs         := regs;
        
        gs_pages        := mem;
        gs_callstack    := cs;
        gs_flags        := flags;
        
      |}
      {|
        gs_regs         := new_regs;
        
        gs_pages        := mem;
        gs_callstack    := cs;
        gs_flags        := flags;
      |} s1 s2 ->
    step (OpContextThis out_arg) s1 s2
(**  

# ContextCaller

## Abstract Syntax

[OpContextCaller (out: out_reg)]

## Syntax 

```
context.caller out
```

## Summary

Retrieves the address of the contract which has called the currently executed contract.


## Semantic

- Fetch the address of the currently executed contract from the active external frame.
- Widen address is widened to [word_bits], zero-extended, and written to register `out`.


## Affected parts of VM state

- registers : `out` register is modified.

## Usage

On delegatecall this address is preserved to be the caller of the caller.
See [FarCall.select_sender].

## Similar instructions

See [OpContextThis], [OpContextCodeAddress].

## Encoding

- Shares opcode with other `contextX` instructions.

 *)
| step_ContextCaller:
  forall flags cs regs (out_arg:out_reg) sender_addr new_regs mem s1 s2,
    store_reg regs
      out_arg (IntValue sender_addr)
      new_regs ->
    
    sender_addr = resize contract_address_bits word_bits (topmost_extframe cs).(ecf_msg_sender) ->

    step_xstate_only
      {|
        gs_regs         := regs;

        
        gs_pages        := mem;
        gs_callstack    := cs;
        gs_flags        := flags;
        
      |}
      {|
        gs_regs         := new_regs;


        
        gs_pages        := mem;
        gs_callstack    := cs;
        gs_flags        := flags;
      |} s1 s2 ->
    step (OpContextCaller out_arg) s1 s2
(**  

# ContextCodeAddress

## Abstract Syntax

[OpContextCodeAddress (out: out_reg)]

## Syntax 

```
context.code_address out
```

## Summary

Retrieves the address of the contract code that is actually being executed.

## Semantic

- Fetch the contract address of the currently executed code from the active external frame.
- Widen the address to [word_bits], zero-extended, and write to register `out`.


## Affected parts of VM state

- registers : `out` register is modified.

## Usage

- In the execution frame created by [OpDelegateCall] this will be the address of the contract that was called by [OpDelegateCall]. 
- Necessary to implement Solidity’s `immutable` under [OpDelegateCall].


## Similar instructions

See [OpContextThis], [OpContextCaller].

## Encoding

- Shares opcode with other `contextX` instructions.

 *)
| step_ContextCodeAddress:
  forall flags  cs regs (out:out_reg) code_addr new_regs mem s1 s2,
    store_reg regs out (IntValue code_addr) new_regs ->
    
    code_addr = resize contract_address_bits word_bits (topmost_extframe cs).(ecf_code_address) ->
    
    step_xstate_only
      {|
        gs_regs         := regs;
        gs_pages        := mem;
        
        gs_callstack    := cs;
        gs_flags        := flags;
        
      |}
      {|
        gs_regs         := new_regs;


        
        gs_pages        := mem;
        gs_callstack    := cs;
        gs_flags        := flags;
      |} s1 s2 ->
    step (OpContextCodeAddress out) s1 s2

(**  

# ContextErgsLeft

## Abstract Syntax

[OpContextErgsLeft (out: out_reg)]

## Syntax 

```
context.ergs_left out
```

## Summary

Retrieves the balance in the current frame.


## Semantic

- Fetch the current balance in ergs from the topmost frame, external or internal.
  The `ergs` belonging to the parent frames are not counted.
- Widen the ergs number to [word_bits], zero-extended, and write to `out`.

## Affected parts of VM state

- registers : `out` register is modified.

## Usage

- Check if the number of ergs is sufficient for an expensive task.
- Should be used before [OpPrecompileCall].


## Similar instructions

The `context` instruction family. 

## Encoding

- Shares opcode with other `contextX` instructions.

 *)
| step_ContextErgsLeft:
  forall flags mem cs regs (out_arg:out_reg) balance new_regs s1 s2,
    store_reg regs out_arg (IntValue balance) new_regs ->
    
    balance = resize _ word_bits (ergs_remaining cs) ->
    step_xstate_only
      {|
        gs_regs         := regs;
        
        gs_pages        := mem;
        gs_callstack    := cs;
        gs_flags        := flags;
        
      |}
      {|
        gs_regs         := new_regs;

        
        gs_pages        := mem;
        gs_callstack    := cs;
        gs_flags        := flags;
      |} s1 s2 ->

    step (OpContextErgsLeft out_arg) s1 s2
         
(**  

# ContextSP

## Abstract Syntax

[OpContextSp (out: out_reg)]

## Syntax

```
context.sp out
```

## Summary

Retrieves current stack pointer.


## Semantic

- Fetch the current SP from the topmost frame, external or internal.
- Widen the SP value to [word_bits], zero-extended, and write to `out`.

## Affected parts of VM state

- registers : `out` register is modified.

## Usage

- Check if the number of ergs is sufficient for an expensive task.
- Should be used before [OpPrecompileCall].


## Similar instructions

The `context` instruction family. 

## Encoding

- Shares opcode with other `contextX` instructions.

 *)
| step_ContextSP:
  forall flags  cs regs (out_arg:out_reg) sp new_regs mem s1 s2,
    store_reg regs out_arg (IntValue sp) new_regs ->
    
    sp = resize _ word_bits (sp_get cs) ->
    
    step_xstate_only
      {|
        gs_regs         := regs;
        gs_pages        := mem;
        
        gs_callstack    := cs;
        gs_flags        := flags;
        
      |}
      {|
        gs_regs         := new_regs;

        
        gs_pages        := mem;

        
        gs_callstack    := cs;
        gs_flags        := flags;
      |} s1 s2 ->
    step (OpContextSp out_arg) s1 s2
(**  
             
# ContextGetContextU128


## Abstract Syntax

[OpContextGetContextU128 (out: out_reg)]

## Syntax 

```
context.get_context_u128 out
```

## Summary

Retrieves current captured context value from the active external frame.

Does not interact with the context register.

## Semantic

- Fetch the current context value from the active external frame.
- Widen the context value from 128 bits to [word_bits], zero-extended, and write to `out`.

## Affected parts of VM state

- registers : `out` register is modified.

## Usage

- See [gs_context_u128], [ecf_context_u128_value].

## Similar instructions

- The `context` instruction family. 
- Farcalls capture context. See [OpFarCall], [OpMimicCall], [OpDelegateCall].

## Encoding

- Shares opcode with other `contextX` instructions.

 *) 
| step_ContextGetContextU128:
  forall flags cs regs (out_arg:out_reg) new_regs mem wcontext s1 s2,
    store_reg regs out_arg (IntValue wcontext) new_regs ->

    wcontext = resize _ word_bits (gs_context_u128 s1) ->  
    
    step_xstate_only
      {|
        gs_regs         := regs;
        gs_pages        := mem;
        
        gs_callstack    := cs;
        gs_flags        := flags;
        
      |}
      {|
        gs_regs         := new_regs;
        gs_pages        := mem;

        
        gs_callstack    := cs;
        gs_flags        := flags;
      |} s1 s2 ->
    step (OpContextGetContextU128 out_arg) s1 s2
(**  
             
# ContextSetContextU128

- Only in kernel mode.
- Forbidden in static calls.

## Abstract Syntax

[OpContextSetContextU128 (in: in_reg)]

## Syntax 

```
context.set_context_u128 out
```

## Summary

Sets context register.

Does not interact with the captured context value in the active external frame.

## Semantic

- Fetch the value from `out` and shrink it to 128 bits.
- Store the shrunk value in the context register [gs_context_u128].

## Affected parts of VM state

- registers : `out` register is modified.

## Usage

- See [gs_context_u128], [ecf_context_u128_value].

## Similar instructions

- The `context` instruction family. 
- Farcalls capture context. See [OpFarCall], [OpMimicCall], [OpDelegateCall].

## Encoding

- Shares opcode with other `contextX` instructions.

 *)
| step_ContextSetContextU128:
  forall gs old_context_u128 regs (in_arg:in_reg) any_tag val new_context_u128 xstate,
    load_reg regs in_arg (mk_pv any_tag val) ->

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
(**  
             
# ContextMeta

VM internal state introspection.

## Abstract Syntax

[OpContextMeta (out: out_reg)]

## Syntax 

```
context.meta out
```

## Summary

Fetches 

## Semantic

- Stores the encoded value of [ABI.MetaParameters.params] in `out`. They follow the structure:

```
Record params := {
      ergs_per_pubdata_byte: ergs;
      heap_size: mem_address;
      aux_heap_size: mem_address;
      this_shard_id: shard_id;
      caller_shard_id: shard_id;
      code_shard_id: shard_id;
    }.
```

## Affected parts of VM state

- registers : `out` register is modified.

## Usage TODO


## Similar instructions

- The `context` instruction family. 

## Encoding

- Shares opcode with other `contextX` instructions.

 *)
| step_ContextMeta:
  forall flags  mem cs regs (out_arg:out_reg) new_regs meta_encoded
    (s1 s2: state),
    store_reg regs
      out_arg (IntValue meta_encoded)
      new_regs ->

    let shards := (topmost_extframe cs).(ecf_shards) in 
    meta_encoded =
      MetaParameters.ABI.(encode)
                           {|
                             ergs_per_pubdata_byte := gs_current_ergs_per_pubdata_byte s1;
                             heap_size := heap_bound cs;
                             aux_heap_size := auxheap_bound cs;
                             this_shard_id := shard_this shards;
                             caller_shard_id := shard_caller shards;
                             code_shard_id := shard_code shards;
                           |} ->
    
    step_xstate_only
      {|
        gs_regs         := regs;

        
        gs_pages        := mem;
        gs_callstack    := cs;
        gs_flags        := flags;
        
      |}
      {|
        gs_regs         := new_regs;

        
        gs_pages        := mem;
        gs_callstack    := cs;
        gs_flags        := flags;
      |} s1 s2 ->
    step (OpContextMeta out_arg) s1 s2
(**  
             
# ContextIncrementTxNumber

- Kernel only.
- Forbidden in static context.

## Abstract Syntax

[OpContextIncrementTxNumber]

## Syntax  TODO

```
context.??? out
```

## Summary

Increments the tx number counter in [gs_tx_number_in_block].

## Semantic


## Affected parts of VM state

- only tx counter.

## Usage

Utility in system contracts.

## Similar instructions

- The `context` instruction family. 

## Encoding

- Shares opcode with other `contextX` instructions.

 *)
         
| step_ContextIncTx:
  forall context_u128 gs new_gs xstate,
    global_state_increment_tx tx_inc gs new_gs -> 
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
(**  
             
# SetErgsPerPubdataByte

- Kernel only.
- Forbidden in static context.

## Abstract Syntax

[OpContextSetErgsPerPubdataByte (value:in_reg)]

## Syntax  TODO

```
context.??? in  
```

## Summary

Sets a new value to [gs_current_ergs_per_pubdata_byte].
## Semantic


## Affected parts of VM state

- only [gs_current_ergs_per_pubdata_byte].

## Usage

Utility in system contracts.

## Similar instructions

- The `context` instruction family. 

## Encoding

- Shares opcode with other `contextX` instructions.

 *)
         
| step_ContextSetErgsPerPubdata:
  forall gs new_gs context_u128 regs (in_arg:in_reg) any_tag new_val (new_val_arg:in_reg) xstate ,

    load_reg regs in_arg (mk_pv any_tag new_val) ->

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
