Require SemanticCommon.

Import Common CoreSet Modifiers SemanticCommon PrimitiveValue.

Section AndDefinition.
  Open Scope ZMod_scope.

  Generalizable Variables op tag.

  Inductive step_and: instruction -> flags_tsmallstep :=
(** {{{!
describe(descr_ins_generic_bitwise(
abstract_name = "OpAnd",
mnemonic = "and"
))
}}}
   *)

  | step_And:
    forall mod_sf old_flags new_flags result,
      `(
          result = bitwise_and op1 op2 ->
          new_flags = apply_set_flags mod_sf
                        old_flags
                        (bitwise_flags result) ->

          step_and (OpAnd (mk_pv tag1 op1) (mk_pv tag2 op2) (IntValue result) mod_sf) old_flags new_flags)
  .
  Generalizable No Variables.
End AndDefinition.
