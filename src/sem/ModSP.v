Require SemanticCommon.

Import Addressing Addressing.Coercions Instruction Resolution State SemanticCommon.

Section Def.
  (**

# ModSP

## Abstract Syntax

[%OpModSP (in1: in_any) (out1: out_any)]

## Syntax


```
ModSP in1, out1
```

## Summary

Ignores its operands but adjusts SP if [%RelSpPop] and/or [%RelSPPush] modes are
used.


## Semantic

- Advances PC
- May modify SP if `in` uses `RelSpPop` addressing mode, or `out` uses
  `RelSpPush` mode. Both operands may affect SP simultaneously; the general
  rules apply, so first `in` will affect SP, then `out` will affect SP.
  See [%resolve] and [%resolve_apply].

## Affected parts of VM state

- execution stack : PC is increased; SP may be changed.

## Usage

The primary use is adjusting SP.

## Similar instructions

- If `in` does not use `RelSpPop` and `out` does not use `RelSpPush`, this instruction does nothing, like `NoOp`.

## Encoding

- `ModSP` and `NoOp` have the same encoding.


*)
Generalizable Variables regs flags pages __ ___.
Inductive cs_step : instruction -> callstack_smallstep :=
| step_ModSP:
  forall cs0 cs1 new_cs (in1:in_any) (out1:out_any),
    `(
        resolve_apply regs cs0 in1 (cs1, __) -> (* Account for possible [%RelSpPop]. *)
        resolve_apply regs cs1 out1 (new_cs, ___) -> (* Account for possible [%RelSpPush]. *)
        cs_step (OpModSP in1 out1) cs0 new_cs
      )
.
End Def.
