Require SemanticCommon.

Import Addressing CallStack Core isa.CoreSet Memory Resolution State SemanticCommon PrimitiveValue ZMod.

Section SpSub.

  Open Scope ZMod_scope.
  (* # SpSub
 ## Abstract Syntax

[%OpSpSub (in1: src_pv) (ofs: imm_in)]

 ## Syntax

 ```
 SpSub in1, imm1
 ```

 ## Summary

Subtract `(in1 + imm1)` from SP.

 ## Semantic

 - Advances PC
 - $\mathit{SP_{new} := SP - (in_1 + imm1)}$, but only if there was no overflow.

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
      (intermediate_sp, false) = old_sp + (resize _ stack_address_bits op) ->
      (new_sp, false) = intermediate_sp - ofs->
      new_cs = sp_update new_sp cs0 ->
      step_sp_sub (OpSpSub (mk_pv __ op) ofs) cs0 new_cs
  .

End SpSub.
