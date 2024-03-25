Require sem.SemanticCommon.
Import Arith Core isa.CoreSet PrimitiveValue SemanticCommon spec.

Section RorDefinition.
  Open Scope ZMod_scope.
  Generalizable Variables tag.
  Inductive step_ror: instruction -> flags_tsmallstep :=
  (** {{{!
describe(descr_ins_generic_bitwise(
abstract_name = "OpRor",
mnemonic = "Ror",
summary = r"""
Bitwise circular right shift of `in1` by the number of binary digits specified by the
lowest byte of `in2`. New binary digits (most significant bits in `out`) are
taken from the least significant bits of `in1`.
""",

semantic = """
- `result = in1 >>> (in2 mod 256)`, where `>>>` is a circular right shift.
- flags are computed as follows:
   - `EQ` is set if $result = 0$.
   - other flags are reset
""",

usage = """
- Operations with bit masks.
- Fast arithmetic.
"""
))
}}}*)
  | step_Ror:
    forall mod_sf result op shift w_shift old_flags new_flags,
      `(w_shift = widen word_bits (low 8 shift) ->
      result = rorBn op (toNat w_shift) ->
      step_ror (OpRor (mk_pv tag1 op) (mk_pv tag2 shift) (IntValue result) mod_sf) old_flags new_flags)
  .
End RorDefinition.
