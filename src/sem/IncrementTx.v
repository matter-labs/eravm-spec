Require SemanticCommon.

Import ABI Bool Coder Core Common Predication Ergs CallStack TransientMemory MemoryOps isa.CoreSet State
  Addressing.Coercions PrimitiveValue SemanticCommon.

Section IncrementTxDefinition.

Inductive step_increment_tx: @instruction bound -> smallstep :=
(** # ContextIncrementTxNumber

- Kernel only.
- Forbidden in static context.

## Abstract Syntax

[%OpIncrementTxNumber]

## Syntax

```
inctx
```

## Legacy Syntax

```
context.inc_tx_num out
```

## Summary

- Reset all transient storage.
- Increment the tx number counter in [%gs_tx_number_in_block].

## Semantic

TODO

## Affected parts of VM state

- Tx counter.
- Transient storages.

## Usage

Utility in system contracts.

## Similar instructions

- The `context` instruction family.

## Encoding

- A variant of `context` [%mach_instruction].

 *)
(* FIXME: clear transient storage *)
| step_IncrementTx:
  forall transient gs new_gs,
    global_state_increment_tx tx_inc gs new_gs ->
    step_increment_tx OpIncrementTxNumber
         {|
           gs_transient    := transient;
           gs_global       := gs;
         |}
         {|
           gs_transient    := transient;
           gs_global       := new_gs;
         |}
.

End IncrementTxDefinition.
