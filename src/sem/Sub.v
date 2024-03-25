Require SemanticCommon.

Import Bool Common Flags CoreSet TransientMemory Modifiers State
  PrimitiveValue SemanticCommon.
Import ssreflect.tuple ssreflect.eqtype.

Section SubDefinition.
  Open Scope ZMod_scope.

  Generalizable Variables op tag.

  Inductive step_sub: instruction -> flags_tsmallstep :=

    (** {{{!
describe(InstructionDoc(

ins=ins_arith("OpSub", "sub"),

summary = """
Unsigned overflowing subtraction of two numbers modulo $2^{256}$.
""",

semantic = r"""
 - result is computed by unsigned subtraction of two numbers with overflow modulo $2^{256}$.

   $$result := \begin{cases}op_1 - op_2 & , \text{if}\  op_1 \geq op_2\\ 2^{256} -  (op_2 - op_1) &, \text{if}\ op_1 \lt op_2\end{cases}$$

- flags are computed as follows:
   - `LT_OF` is set if overflow occurs, i.e. $op_1 \lt op_2$
   - `EQ` is set if $result = 0$.
   - `GT` is set if both `LT_OF` and `EQ` are cleared.
""",

usage = """
- Arithmetic operations.
""",

similar = """
Flags are computed exactly as in `add`, but the meaning of overflow is different
for addition and subtraction.
"""
))
}}}
   *)
  | step_Sub:
    forall mod_sf old_flags new_flags,
      `(
          let (new_OF, result) := op1 - op2 in
          let new_EQ := result == zero256 in
          let new_GT := negb new_EQ && negb new_OF in

          new_flags = apply_set_flags mod_sf
                        old_flags
                        (bflags new_OF new_EQ new_GT) ->

          step_sub (OpSub (mk_pv tag1 op1) (mk_pv tag2 op2) (IntValue result) mod_sf) old_flags new_flags)
  .
  Generalizable No Variables.
End SubDefinition.
