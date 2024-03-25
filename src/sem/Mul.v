Require sem.SemanticCommon.

Import Bool Core Modifiers Common Flags isa.CoreSet CallStack TransientMemory MemoryOps State
  ZArith PrimitiveValue SemanticCommon List ListNotations.

Import ssreflect.eqtype ssreflect.tuple.

Section MulDefinition.
  Open Scope ZMod_scope.

  Generalizable Variables tag.

  Inductive step_mul: instruction -> flags_tsmallstep :=
(** {{{!
describe(InstructionDoc(

ins=ins_arith("OpMul", "mul", hasOut2 = True),

summary = """
Unsigned multiplication of two numbers modulo $2^{512}$; the high and low 256
bits of the result are returned in two separate operands.
""",

semantic = r"""
1. Compute result by unsigned multiplication of `in1` by `in2`.

   $$\begin{cases}result_{high} := \frac{ op_1 \times op_2}{2^{256}}\\
result_{low} := op_1 \times op_2 \mod 2^{256} \end{cases}$$

2. Flags are computed as follows:
   - `LT_OF` is set if overflow occurs, i.e. $op_1 \times op_2 \geq 2^{256}$
   - `EQ` is set if $result_{low} = 0$.
   - `GT` is set if `LT_OF` and `EQ` are cleared.
""",

usage = """
- Arithmetic operations.
""",

similar = """
- See [%OpDiv].
"""
))}}}
 *)
  | step_Mul:
    forall mod_sf old_flags new_flags high low high256 low256 op1 op2,
      `(
          high256 = high 256 (op1*op2) ->
          low256  = low 256 (op1*op2) ->

          let new_EQ := low256  == zero256 in
          let new_OF := high256 != zero256 in
          let new_GT := negb new_EQ && negb new_OF in

          new_flags = apply_set_flags mod_sf old_flags
                        (bflags new_OF new_EQ new_GT) ->

          step_mul (OpMul (mk_pv tag1 op1) (mk_pv tag2 op2) (IntValue low256) (IntValue high256) mod_sf) old_flags new_flags
        ).
  Generalizable No Variables.
End MulDefinition.
