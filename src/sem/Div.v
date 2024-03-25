Require sem.SemanticCommon.

Import Addressing Bool ZArith Common Flags GPR isa.CoreSet CallStack Modifiers State
  ZBits Addressing.Coercions PrimitiveValue SemanticCommon List ListNotations.

Section DivDefinition.
  Open Scope Z_scope.

  Generalizable Variables tag.

  Inductive step_div: instruction -> flags_tsmallstep :=

(** {{{!
describe(InstructionDoc(

ins=ins_arith("OpDiv", "div", hasOut2 = True),

summary = """
Unsigned division of `in1` by `in2`. The quotient is returned in `out1`, the
remainder is returned in `out2`.
""",

semantic = r"""
- If `in2` $\neq 0$:
     $$\begin{cases}out_1 := \frac{ op_1}{op_2} \\
out_{2} := \text{rem } op_1 \ op_2 \end{cases}$$

  Flags are computed as follows:
  - `LT_OF` is cleared;
  - `EQ` is set if the quotient is zero;
  - `GT` is set if the reminder is zero.

- If `in2` $= 0$:
   $$\begin{cases}out_1 := 0 \\ out_{2} := 0 \end{cases}$$

   Flags are computed as follows:
   - `LT_OF` is set.
   - `EQ` is set if $result_{low} = 0$.
   - `GT` is set if `LT_OF` and `EQ` are cleared.
""",

usage = """
- Arithmetic operations.
""",

similar = """
- See [%OpMul].
"""
))
}}}
   *)
  | step_Div_no_overflow:
    `(forall mod_sf old_flags new_flags w_quot w_rem quot rem (x y:Z) op1 op2,
          x = toZ op1 ->
          y = toZ op2 ->
          y <> 0 ->
          quot = Z.div x y ->
          rem = Z.rem x y ->
          w_quot = u256_of quot ->
          w_rem = u256_of rem ->

          let new_EQ := quot =? 0 in
          let new_GT := rem =? 0 in
          new_flags = apply_set_flags mod_sf
                        old_flags
                        (bflags false new_EQ new_GT) ->

          step_div (OpDiv (mk_pv tag1 op1) (mk_pv tag2 op2) (IntValue w_quot) (IntValue w_rem) mod_sf) old_flags new_flags)
  | step_Div_overflow:
    forall mod_sf old_flags new_flags (x y:Z) op1 op2,
      `(
          x = toZ op1 ->
          y = toZ op2 ->
          new_flags = apply_set_flags mod_sf old_flags (bflags true false false) ->

          step_div (OpDiv (mk_pv tag1 op1) (mk_pv tag2 op2) (IntValue zero256) (IntValue zero256) mod_sf) old_flags new_flags
        )
.
End DivDefinition.
