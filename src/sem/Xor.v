Require SemanticCommon.

Import Common CoreSet Modifiers SemanticCommon PrimitiveValue.

Section XorDefinition.
  Open Scope ZMod_scope.

  Generalizable Variables op tag.

  Inductive step_xor: instruction -> flags_tsmallstep :=
    (** {{{!
describe(descr_ins_generic_bitwise(
abstract_name = "OpXor",
mnemonic = "xor"
))
}}}
   *)

  | step_Xor:
    forall mod_sf old_flags new_flags result,
      `(
          result = bitwise_xor op1 op2 ->
          new_flags = apply_set_flags mod_sf
                        old_flags
                        (bitwise_flags result) ->

          step_xor (OpXor (mk_pv tag1 op1) (mk_pv tag2 op2) (IntValue result) mod_sf) old_flags new_flags)
  .


End XorDefinition.
