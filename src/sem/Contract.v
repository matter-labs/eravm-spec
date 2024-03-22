From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Coder Core Common Predication Ergs CallStack TransientMemory MemoryOps isa.CoreSet State
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations ABI.MetaParametersABI.

Section ContractDefinitions.
(** # ContractThis

## Abstract Syntax

[%OpContractThis (out: out_reg)]

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

See [%OpContractCaller], [%OpContractCodeAddress].

## Encoding

- A variant of `context` [%mach_instruction].

 *)
Inductive step_contract: instruction -> smallstep :=

| step_ContractThis:
  forall this_addr (this_addr_word:word) (s1 s2: state),

    this_addr = ecf_this_address (active_extframe (gs_callstack s1)) ->
    this_addr_word = widen word_bits this_addr ->


    step_contract (OpContractThis (IntValue this_addr_word)) s1 s2
(** # ContractCaller

## Abstract Syntax

[%OpContractCaller (out: out_reg)]

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

See [%OpContractThis], [%OpContractCodeAddress].

## Encoding

- A variant of `context` [%mach_instruction].

 *)
| step_ContractCaller:
  forall sender_addr sender_addr_word (s1 s2:state),
    sender_addr = (active_extframe (gs_callstack s1)).(ecf_msg_sender) ->
    sender_addr_word = widen word_bits sender_addr ->

    step_contract (OpContractCaller (IntValue sender_addr_word)) s1 s2
(** # ContractCodeAddress

## Abstract Syntax

[%OpContractCodeAddress (out: out_reg)]

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

See [%OpContractThis], [%OpContractCaller].

## Encoding

- A variant of `context` [%mach_instruction].

 *)
| step_ContractCodeAddress:
  forall code_addr code_addr_word (s1 s2:state),
    code_addr = ecf_code_address (active_extframe (gs_callstack s1)) ->
    code_addr_word = widen word_bits code_addr ->
    step_contract (OpContractCodeAddress (IntValue code_addr_word)) s1 s2.

End ContractDefinitions.
