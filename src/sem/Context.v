From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Coder Core Common Predication Ergs CallStack Memory MemoryOps isa.CoreSet State
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations ABI.MetaParametersABI.

Section ContextDefinitions.
(** # ContextThis

## Abstract Syntax

[%OpContextThis (out: out_reg)]

## Syntax

```
context.this out
```

## Summary

Retrieves the address of the currently executed contract.

## Semantic

- Fetch the address of the currently executed contract
from the active external frame.
- Widen the address to [%word_bits], zero-extended, and write to register `out`.


## Affected parts of VM state

- registers : `out` register is modified.

## Usage

On [%OpDelegateCall] this address is preserved to be one of the caller.
See [%select_this_address].

## Similar instructions

See [%OpContextCaller], [%OpContextCodeAddress].

## Encoding

- A variant of `context` [%mach_instruction].

 *)
Inductive step_context: instruction -> smallstep :=

| step_ContextThis:
  forall this_addr (this_addr_word:word) (s1 s2: state),

    this_addr = ecf_this_address (active_extframe (gs_callstack s1)) ->
    this_addr_word = widen word_bits this_addr ->


    step_context (OpContextThis (IntValue this_addr_word)) s1 s2
(** # ContextCaller

## Abstract Syntax

[%OpContextCaller (out: out_reg)]

## Syntax

```
context.caller out
```

## Summary

Retrieves the address of the contract which has called the currently executed contract.


## Semantic

- Fetch the address of the currently executed contract from the active external frame.
- Widen address is widened to [%word_bits], zero-extended, and written to register `out`.


## Affected parts of VM state

- registers : `out` register is modified.

## Usage

On [%OpDelegateCall] this address is preserved to be the caller of the caller.
See [%select_sender].

## Similar instructions

See [%OpContextThis], [%OpContextCodeAddress].

## Encoding

- A variant of `context` [%mach_instruction].

 *)
| step_ContextCaller:
  forall sender_addr sender_addr_word (s1 s2:state),
    sender_addr = (active_extframe (gs_callstack s1)).(ecf_msg_sender) ->
    sender_addr_word = widen word_bits sender_addr ->

    step_context (OpContextCaller (IntValue sender_addr_word)) s1 s2
(** # ContextCodeAddress

## Abstract Syntax

[%OpContextCodeAddress (out: out_reg)]

## Syntax

```
context.code_source out
```

## Summary

Retrieves the address of the contract code that is actually being executed.

## Semantic

- Fetch the contract address of the currently executed code from the active external frame.
- Widen the address to [%word_bits], zero-extended, and write to register `out`.


## Affected parts of VM state

- registers : `out` register is modified.

## Usage

- In the execution frame created by [%OpDelegateCall] this will be the address of the contract that was called by [%OpDelegateCall].
- Necessary to implement Solidity’s `immutable` under [%OpDelegateCall].


## Similar instructions

See [%OpContextThis], [%OpContextCaller].

## Encoding

- A variant of `context` [%mach_instruction].

 *)
| step_ContextCodeAddress:
  forall code_addr code_addr_word (s1 s2:state),
    code_addr = ecf_code_address (active_extframe (gs_callstack s1)) ->
    code_addr_word = widen word_bits code_addr ->
    step_context (OpContextCodeAddress (IntValue code_addr_word)) s1 s2

(** # ContextErgsLeft

## Abstract Syntax

[%OpContextErgsLeft (out: out_reg)]

## Syntax

```
context.ergs_left out
```

## Summary

Retrieves the number of ergs allocated for the current frame.


## Semantic

- Fetch the currently allocated ergs from the topmost frame, external or internal.
  The `ergs` belonging to the parent frames are not counted.
- Widen the ergs number to [%word_bits], zero-extended, and write to `out`.

## Affected parts of VM state

- registers : `out` register is modified.

## Usage

- Check if the number of ergs is sufficient for an expensive task.
- Should be used before [%OpPrecompileCall].


## Similar instructions

The `context` instruction family.

## Encoding

- A variant of `context` [%mach_instruction].

 *)
| step_ContextErgsLeft:
  forall ergs_left_word (s1 s2:state),
    ergs_left_word = widen word_bits (ergs_remaining (gs_callstack s1)) ->
    step_context (OpContextErgsLeft (IntValue ergs_left_word)) s1 s2

(** # ContextSP

## Abstract Syntax

[%OpContextSp (out: out_reg)]

## Syntax

```
context.sp out
```

## Summary

Retrieves current stack pointer.


## Semantic

- Fetch the current SP from the topmost frame, external or internal.
- Widen the SP value to [%word_bits], zero-extended, and write to `out`.

## Affected parts of VM state

- registers : `out` register is modified.

## Usage

- Check if the number of ergs is sufficient for an expensive task.
- Should be used before [%OpPrecompileCall].


## Similar instructions

The `context` instruction family.

## Encoding

- A variant of `context` [%mach_instruction].

 *)
| step_ContextSP:
  forall sp_zero_padded (s1 s2 :state),
    sp_zero_padded = widen word_bits (sp_get (gs_callstack s1)) ->

    step_context (OpContextSp (IntValue sp_zero_padded)) s1 s2
(** # ContextGetContextU128


## Abstract Syntax

[%OpContextGetContextU128 (out: out_reg)]

## Syntax

```
context.get_context_u128 out
```

## Summary

Retrieves current captured context value from the active external frame.

Does not interact with the context register.

## Semantic

- Fetch the current context value from the active external frame.
- Widen the context value from 128 bits to [%word_bits], zero-extended, and write to `out`.

## Affected parts of VM state

- registers : `out` register is modified.

## Usage

- See [%gs_context_u128], [%ecf_context_u128_value].

## Similar instructions

- The `context` instruction family.
- Farcalls capture context. See [%OpFarCall], [%OpMimicCall], [%OpDelegateCall].

## Encoding

- A variant of `context` [%mach_instruction].

 *)
| step_ContextGetContextU128:
  forall wcontext (s1 s2: state),
    wcontext = widen word_bits (gs_context_u128 s1) ->
    step_context (OpContextGetContextU128 (IntValue wcontext)) s1 s2
(** # ContextSetContextU128

- Only in kernel mode.
- Forbidden in static calls.

## Abstract Syntax

[%OpContextSetContextU128 (in: in_reg)]

## Syntax

```
context.set_context_u128 out
```

## Summary

Sets context register.

Does not interact with the captured context value in the active external frame.

## Semantic

- Fetch the value from `out` and narrow it to 128 bits.
- Store the shrunk value in the context register [%gs_context_u128].

## Affected parts of VM state

- registers : `out` register is modified.

## Usage

- See [%gs_context_u128], [%ecf_context_u128_value].

## Similar instructions

- The `context` instruction family.
- Farcalls capture context. See [%OpFarCall], [%OpMimicCall], [%OpDelegateCall].

## Encoding

- A variant of `context` [%mach_instruction].

 *)
| step_ContextSetContextU128:
  forall (new_context256 :word) any_tag (new_context_u128:u128) xs1 xs2 s1 s2,
    new_context_u128 = low 128 new_context256->
    xs2 = xs1 <| gs_context_u128 := new_context_u128 |> ->
    step_transient_only xs1 xs2 s1 s2 ->

    step_context (OpContextSetContextU128 (mk_pv any_tag new_context256)) s1 s2
(** # ContextMeta

VM internal state introspection.

## Abstract Syntax

[%OpContextMeta (out: out_reg)]

## Syntax

```
context.meta out
```

## Summary

Fetches

## Semantic

- Stores the encoded value of [%MetaParametersABI] in `out`. They follow the structure:

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

## Similar instructions

- The `context` instruction family.

## Encoding

- A variant of `context` [%mach_instruction].

 *)
| step_ContextMeta:
  forall params cs shards
    (s1 s2: state),
    cs = gs_callstack s1 ->
    shards = (active_extframe cs).(ecf_shards) ->
    params = {|
               ergs_per_pubdata_byte := gs_current_ergs_per_pubdata_byte s1;
               heap_size := heap_bound cs;
               aux_heap_size := auxheap_bound cs;
               this_shard_id := shard_this shards;
               caller_shard_id := shard_caller shards;
               code_shard_id := shard_code shards;
             |} ->
    step_context (OpContextMeta (Some (IntValue params))) s1 s2
(** # ContextIncrementTxNumber

- Kernel only.
- Forbidden in static context.

## Abstract Syntax

[%OpContextIncrementTxNumber]

## Syntax

```
context.inc_tx_num out
```

## Summary

Increments the tx number counter in [%gs_tx_number_in_block].

## Semantic


## Affected parts of VM state

- only tx counter.

## Usage

Utility in system contracts.

## Similar instructions

- The `context` instruction family.

## Encoding

- A variant of `context` [%mach_instruction].

 *)

| step_ContextIncTx:
  forall transient gs new_gs,
    global_state_increment_tx tx_inc gs new_gs ->
    step_context OpContextIncrementTxNumber
         {|
           gs_transient    := transient;
           gs_global       := gs;
         |}
         {|
           gs_transient    := transient;
           gs_global       := new_gs;
         |}
(** # SetErgsPerPubdataByte

- Kernel only.
- Forbidden in static context.

## Abstract Syntax

[%OpContextSetErgsPerPubdataByte (value:in_reg)]

## Syntax

```
context.set_ergs_per_pubdata in
```

## Summary

Sets a new value to [%gs_current_ergs_per_pubdata_byte].

## Semantic


## Affected parts of VM state

- only [%gs_current_ergs_per_pubdata_byte].

## Usage

Utility in system contracts.

## Similar instructions

- The `context` instruction family.

## Encoding

- A variant of `context` [%mach_instruction].

 *)

| step_ContextSetErgsPerPubdata:
  forall gs new_gs any_tag new_val transient ,

    let new_ergs := low ergs_bits new_val in
    new_gs = gs <| gs_global ::= (fun s => s <| gs_current_ergs_per_pubdata_byte := new_ergs |> ) |> ->

    step_context (OpContextSetErgsPerPubdataByte (mk_pv any_tag new_val))
        {|
          gs_transient    := transient;
          gs_global       := gs;
        |}
        {|
          gs_transient    := transient;
          gs_global       := new_gs;
        |}

.
End ContextDefinitions.
