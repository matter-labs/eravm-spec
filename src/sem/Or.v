Require SemanticCommon.

Import Common CoreSet Modifiers SemanticCommon PrimitiveValue.

Section OrDefinition.
  Open Scope ZMod_scope.

  Generalizable Variables op tag.

  Inductive step_or: instruction -> flags_tsmallstep :=
(** {{{!
describe(descr_ins_generic_bitwise(
abstract_name = "OpOr",
mnemonic = "or"
))
}}}
   *)
  | step_Or:
    forall mod_sf old_flags new_flags result,
      `(
          result = bitwise_or op1 op2 ->
          new_flags = apply_set_flags mod_sf
                        old_flags
                        (bitwise_flags result) ->

          step_or (OpOr (mk_pv tag1 op1) (mk_pv tag2 op2) (IntValue result) mod_sf) old_flags new_flags)
  .

  Generalizable No Variables.
End OrDefinition.
