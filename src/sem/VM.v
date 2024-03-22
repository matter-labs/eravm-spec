From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Coder Core Common Predication Ergs CallStack TransientMemory MemoryOps isa.CoreSet State
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations ABI.MetaParametersABI.

Section VMDefinitions.

  Inductive step_vm: instruction -> smallstep :=
  (** # VMErgsLeft

## Abstract Syntax

[%OpVMErgsLeft (out: out_reg)]

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
  | step_VMErgsLeft:
    forall ergs_left_word (s1 s2:state),
      ergs_left_word = widen word_bits (ergs_remaining (gs_callstack s1)) ->
      step_vm (OpVMErgsLeft (IntValue ergs_left_word)) s1 s2

  (** # VMSP

## Abstract Syntax

[%OpVMSp (out: out_reg)]

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
  | step_VMSP:
    forall sp_zero_padded (s1 s2 :state),
      sp_zero_padded = widen word_bits (sp_get (gs_callstack s1)) ->

      step_vm (OpVMSP (IntValue sp_zero_padded)) s1 s2

  (** # VMMeta

VM internal state introspection.

## Abstract Syntax

[%OpVMMeta (out: out_reg)]

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
  | step_VMMeta:
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
      step_vm (OpVMMeta (Some (IntValue params))) s1 s2
  .
End VMDefinitions.
