From RecordUpdate Require Import RecordSet.
From mathcomp Require Import ssreflect eqtype.
From Bits Require Import bits spec tuple spec.properties.
Require SemanticCommon Semantics sem.Jump.

Import Addressing Bool Core Common Predication GPR CallStack Memory MemoryOps isa.CoreSet State
  PrimitiveValue SemanticCommon Semantics RecordSetNotations.
Import Addressing.Coercions.
Import ssreflect.tuple.

Section JumpTests.
  Generalizable All Variables.
  Theorem jump_correct1 :
    forall tail,
      let ins := Assembly.OpJump R0 in
      `(

          let topframe0 := InternalCall (mk_cf eh sp ( # 2) (# 10) cp) tail in
          let topframe1 := InternalCall (mk_cf eh sp ( # 0) (# 4) cp) tail in
          execute_action Execute
            (AssemblyToCore.to_core ins)
            (mk_state
               (mk_transient_state flags regs pges topframe0 context_u128 st)
               gs)

            (mk_state
               (mk_transient_state flags regs pges topframe1 context_u128 st)
               gs)
        )
  .
  Proof.
    move=> tail ins eh sp cp flags regs pges context_u128 st gs topframe new_topframe.
    {
      econstructor; first by reflexivity.
      {
        econstructor; reflexivity.
      }
      {
        constructor.
        unfold ergs_remaining, usub_uf, cf_ergs_remaining, cfc, gs_callstack, pc_map.
        instantiate (1:= # 4).
        by apply /eqP /andP.
      }
      {
        repeat econstructor.
      }
      {
        simpl.
        econstructor.
        {
          do  10 (constructor 2).
          by constructor 1.
        }
        {
          instantiate (1:= ergs_set #4 topframe).

          econstructor.
          simpl.
          subst topframe.
          subst new_topframe.
          instantiate (1:=pges).
          instantiate (1:=regs).

          econstructor; last by constructor.
          econstructor; [|reflexivity|reflexivity].
          econstructor.
          unfold pc_set, pc_map.
          unfold code_address_bits.
          simpl.
          by f_equal.
        }
      }
    }
  Qed.

End JumpTests.
