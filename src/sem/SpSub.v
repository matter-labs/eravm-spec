Require SemanticCommon.

Import Arith Addressing CallStack Core isa.CoreSet TransientMemory Resolution State SemanticCommon PrimitiveValue spec.

Section SpSubDefinition.

  Open Scope ZMod_scope.
  (** # SpSub
## Abstract Syntax

[%OpSpSub (in1: in_reg) (ofs: imm_in)]

## Syntax

```
decsp reg+imm
decsp reg
decsp imm
```

## Legacy Syntax

```
nop stack-=[reg+ofs]
```

## Summary

Subtract `(reg + imm)` from SP.

## Semantic

 - Advances PC
 - $\mathit{SP_{new} := SP - (reg + imm)}$, but only if there was no overflow.

## Affected parts of VM state

 - execution stack : PC is increased; SP may be decreased.

## Usage

Adjusting SP e.g. deallocating space on stack.


## Similar instructions

[%OpSpSub] subtracts value from SP.

## Encoding

 - `NoOp`, `SpAdd`, `SpSub` are encoded as the same instruction.
   *)
  Inductive step_sp_sub : instruction -> callstack_smallstep :=
  | step_op_sp_sub:
    forall (cs0 new_cs: callstack) (old_sp intermediate_sp new_sp ofs: stack_address) op __,
      sp_get cs0 = old_sp ->
      (false, intermediate_sp) = old_sp + (low stack_address_bits op) ->
      (false, new_sp) = intermediate_sp - ofs->
      new_cs = sp_update new_sp cs0 ->
      step_sp_sub (OpSpSub (mk_pv __ op) ofs) cs0 new_cs
  .

End SpSubDefinition.
