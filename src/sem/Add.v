Require SemanticCommon.

Import Bool Common Flags CoreSet TransientMemory Modifiers State PrimitiveValue SemanticCommon.
Import ssreflect.tuple ssreflect.eqtype.


Section AddDefinition.
  Open Scope ZMod_scope.

  Generalizable Variables op tag.
  Inductive step_add: instruction -> flags_tsmallstep :=
  (** {{{!
describe(InstructionDoc(

ins=ins_arith("OpAdd", "add"),

summary = """
Unsigned overflowing addition of two numbers modulo $2^{256}$.
""",

semantic = r"""
- result is computed by unsigned addition of two numbers with overflow modulo $2^{256}$.

   $$result := op_1 + op_2 \mod 2^{256}$$

- flags are computed as follows:
   - `LT_OF` is set if overflow occurs, i.e. $op_1 + op_2 \geq 2^{256}$
   - `EQ` is set if $result = 0$.
   - `GT` is set if both `LT_OF` and `EQ` are cleared.
""",

usage = """
- Arithmetic operations.
- There is no dedicated `mov` instruction, so `add` is used to copy values
  around. Copying A to B is implemented as `add A, r0, B`.
""",

similar = """
Flags are computed exactly as in `sub`, but the meaning of overflow is different
for addition and subtraction.
"""
))
}}}
   *)
  | step_Add:
    forall mod_sf old_flags new_flags result new_OF,
      `(
          (new_OF, result) = op1 + op2 ->
          let new_EQ := result == zero256 in
          let new_GT := negb new_EQ && negb new_OF in

          new_flags = apply_set_flags mod_sf
                        old_flags
                        (bflags new_OF new_EQ new_GT) ->

          step_add (OpAdd (mk_pv tag1 op1) (mk_pv tag2 op2) (IntValue result) mod_sf) old_flags new_flags)
  .
  Generalizable No Variables.

End AddDefinition.
