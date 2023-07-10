Require sem.BinOps.
Import Addressing Bool BinOps ZArith Common Flags Instruction Memory ZMod
  Addressing.Coercions PrimitiveValue SemanticCommon.

Section Def.
  Open Scope ZMod_scope.

  (** # Bitwise operations  *)
  Inductive binop_bitwise_effect_spec:
    in_any -> in_any -> out_any -> mod_swap -> mod_set_flags ->
    primitive_value -> primitive_value -> primitive_value ->
    xsmallstep :=
  | bseec_apply:
    forall  (in1: in_any) (in2:in_reg) (out: out_any) swap set_flags
       old_state new_state op1 op2 result flags_candidate,
      binop_effect_spec swap set_flags
        (in1, op1) (in2, op2) (out, result) flags_candidate
        old_state new_state ->

      flags_candidate = bflags false (result.(value) == zero256) false ->
      binop_bitwise_effect_spec in1 in2 out swap set_flags op1 op2 result old_state new_state.

End Def.
