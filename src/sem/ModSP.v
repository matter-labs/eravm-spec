Require SemanticCommon.

Import Addressing Addressing.Coercions Instruction Resolution State SemanticCommon.

Section Def.
  (**

# ModSP

## Abstract Syntax

[OpModSP (in1: in_any) (out1: out_any)]

## Syntax


```
ModSP in1, out1
```

## Summary

Ignores its operands but adjusts SP if `RelSpPop` and/or `RelSPPush` modes are
used.


See [Arg.RelSpPush], [Arg.RelSpPop].


## Semantic

- Advances PC
- May modify SP if `in` uses `RelSpPop` addressing mode, or `out` uses
  `RelSpPush` mode. Both operands may affect SP simultaneously; the general
  rules apply, so first `in` will affect SP, then `out` will affect SP.

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
        resolve_apply regs cs0 in1 (cs1, __) -> (* Account for possible [RelSpPop]. *)
        resolve_apply regs cs1 out1 (new_cs, ___) -> (* Account for possible [RelSpPush]. *)
        cs_step (OpModSP in1 out1) cs0 new_cs
      )
.
End Def.
(**

## Examples



 *)
Section Examples.
Import Addressing.Coercions ZMod Memory ZArith CallStack.
Open Scope Z.
Set Printing Coercions.

(**

`modsp stack-=[23], stack+=[88]`

*)

Section Ex1.
  Import GPR.
  (* Coercion int_mod_of : Z >-> int_mod. *)
  (* Let ex := OpModSP (RelSpPop R0 23) (RelSpPush R0 88) : instruction. *)
(* Import ZMod.
Goal
  forall codes flags depot pages xstack0 context_u128 regs,
    step ex
          {|
          gs_callstack    := xstack0;
          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
          |}
          {|
          gs_callstack    := ExecutionStack.sp_mod  (fun sp =>
                                                       fst ((fst (sp + 23)) - 88 )) xstack0;


          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
          |}
.
  Proof.
    intros codes flags depot pages xstack0 context_u128 regs.
    apply step_ModSP with (xstack1 := ExecutionStack.sp_mod (fun sp => fst (sp + 23)) xstack0); simpl.
    - destruct xstack0.
      + simpl.
        destruct c.
        simpl.
        unfold RecordSet.set.
simpl.
        econstructor 1 with (regs := regs) (arg := RelSpPop R0 23).
        * econstructor ; eauto.
          econstructor; eauto.
          constructor.
          constructor.
          constructor.
          simpl.
          reflexivity.
    *)
Fail Check OpModSP (RelSpPush R1 23) (RelSpPush R3 88) : instruction.
End Ex1.
End Examples.
