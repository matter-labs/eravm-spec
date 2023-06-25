Require sem.Bitwise.
Import Addressing ZArith Common Instruction Memory ZMod
  Addressing.Coercions SemanticCommon sem.Bitwise.

Section Def.
  Open Scope ZMod_scope.
  Inductive step: instruction -> smallstep :=
  | step_Rol:
    forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out _tag1 _tag2 x y result gs gs',
      binop_state_bitwise_effect_spec in1 in2 out mod_swap mod_sf
        (mk_pv _tag1 x) (mk_pv _tag2 y) (IntValue result)  gs gs' ->
      result = rol _ x y ->
      step (OpRol in1 in2 out mod_sf) gs gs'
  .

End Def.
