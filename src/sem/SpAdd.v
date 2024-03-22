Require SemanticCommon.

Import Arith Addressing CallStack Core isa.CoreSet TransientMemory Resolution State SemanticCommon PrimitiveValue spec.

Section SpAddDefinition.

  Open Scope ZMod_scope.
(** # SpAdd
## Abstract Syntax

[%OpSpAdd       (in1: in_reg) (ofs: imm_in)]


## Syntax

```
incsp reg+imm
incsp reg
incsp imm
```

## Legacy Syntax

```
nop r0, r0, stack+=[reg+ofs]
```

## Summary

Add `(reg + imm)` to SP.

## Semantic

 - Advances PC
 - $\mathit{SP_{new} := SP + (reg + imm)}$, but only if there was no overflow.

## Affected parts of VM state

 - execution stack : PC is increased; SP may be increased.

## Usage

Adjusting SP e.g. reserving space on stack.


## Similar instructions

[%OpSpSub] subtracts a value from SP.

## Encoding

 - `NoOp`, `SpAdd`, `SpSub` are encoded as the same instruction.
   *)
  Inductive step_sp_add : instruction -> callstack_smallstep :=
  | step_op_sp_add:
    forall (cs0 new_cs: callstack) (old_sp intermediate_sp new_sp ofs: stack_address) op __,
      sp_get cs0 = old_sp ->
      (false, intermediate_sp) = old_sp + (low stack_address_bits op) ->
      (false, new_sp) = intermediate_sp + ofs->
      new_cs = sp_update new_sp cs0 ->
      step_sp_add (OpSpAdd (mk_pv __ op) ofs) cs0 new_cs
  .

End SpAddDefinition.
