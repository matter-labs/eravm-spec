From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Coder Core Common Predication Ergs CallStack TransientMemory MemoryOps isa.CoreSet State
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations ABI.MetaParametersABI.

Section ContextDefinitions.

Inductive step_context: instruction -> smallstep :=
(** # ContextGetContextU128


## Abstract Syntax

[%OpGetCapturedContext (out: out_reg)]

## Syntax

```
ldvl reg
```

## Legacy Syntax

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

- Farcalls capture context. See [%OpFarCall], [%OpMimicCall], [%OpDelegateCall].
- [%OpSetContextReg] to set context register, from where the value is captured by farcalls.

 *)
| step_GetCapturedContext:
  forall wcontext (s1 s2: state),
    wcontext = widen word_bits (gs_context_u128 s1) ->
    step_context (OpGetCapturedContext (IntValue wcontext)) s1 s2
(** # SetContextReg

- Only in kernel mode.
- Forbidden in static calls.

## Abstract Syntax

[%OpContextSetContextU128 (in: in_reg)]

## Syntax

```
stvl out
```

## Legacy Syntax

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

 *)
| step_SetContextReg:
  forall (new_context256 :word) any_tag (new_context_u128:u128) xs1 xs2 s1 s2,
    new_context_u128 = low 128 new_context256->
    xs2 = xs1 <| gs_context_u128 := new_context_u128 |> ->
    step_transient_only xs1 xs2 s1 s2 ->

    step_context (OpSetContextReg (mk_pv any_tag new_context256)) s1 s2.
End ContextDefinitions.
