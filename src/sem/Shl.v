Require sem.SemanticCommon.
Import Arith Core isa.CoreSet PrimitiveValue SemanticCommon spec.

Section ShlDefinition.
  Open Scope ZMod_scope.
  Generalizable Variables tag.
  Import operations operations.BitsNotations.
  Inductive step_shl: instruction -> flags_tsmallstep :=

(** {{{!
describe(descr_ins_generic_bitwise(
abstract_name = "OpShl",
mnemonic = "shl",
summary = r"""
Bitwise left shift of `in1` by the number of binary digits specified by the
lowest byte of `in2`. New binary digits (most significant bits in `out`) are
zeros.
""",

semantic = """
- `result = in1 << (in2 mod 256)`
- flags are computed as follows:
   - `EQ` is set if $result = 0$.
   - other flags are reset
""",

usage = """
- Operations with bit masks.
- Fast arithmetic.
"""
))
}}}
*)
  | step_Shl:
    forall mod_sf result op shift w_shift old_flags new_flags,
      `(shift = toNat (low 8 w_shift) ->
        result = shlBn op shift ->
        step_shl (OpShl (mk_pv tag1 op) (mk_pv tag2 w_shift) (IntValue result) mod_sf) old_flags new_flags)
  .
End ShlDefinition.
