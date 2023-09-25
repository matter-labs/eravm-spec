Require SemanticCommon.

Import Core isa.CoreSet State SemanticCommon.

Section NoOpDefinition.
(** # Nop
## Abstract Syntax

[%OpNoOp]

## Syntax

```
nop
```

## Summary

Do nothing.

## Affected parts of VM state

 - execution stack : PC is increased.

## Similar instructions

[%OpSpAdd], [%OpSpSub] and [%OpNoOp] are translated to [%mach_instruction] with the same [%mach_opcode]. See [%asm_to_mach].

## Encoding

 - `NoOp`, `SpAdd`, `SpSub` are encoded as the same instruction.
   *)
  Inductive step_nop: @instruction bound -> smallstep :=
  | step_NoOp:
    forall s, step_nop OpNoOp s s
  .

End NoOpDefinition.
