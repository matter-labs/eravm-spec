Require sem.SemanticCommon.
Import Core isa.CoreSet PrimitiveValue SemanticCommon ZMod.

Section Shr.
  Open Scope ZMod_scope.
  Generalizable Variables tag.
  Inductive step_shr: instruction -> flags_tsmallstep :=
  (**
# Shr

## Abstract Syntax

[%OpShr (in1: in_any) (in2: in_reg) (out: out_any) (swap:mod_swap) (flags:mod_set_flags)]

## Syntax

- `shr in1, in2, out`
- `shr.s in1, in2, out`, to set `swap` modifier.
- `shr! in1, in2, out`, to set `set flags` modifier.
- `shr.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

## Summary

Bitwise left shift of `in1` by the number of binary digits specified by the lowest byte of `in2`. New binary digits (most significant bits in `out`) are zeros.

## Semantic

Follows the scheme described in [%binop_state_bitwise_effect_spec].

- result is computed as `in1 >> (in2 mod 256)`
- flags are computed as follows:
   - `EQ` is set if $result = 0$.
   - other flags are reset

Reminder: flags are only set if `set_flags` modifier is set. *)
  | step_Shr:
    forall mod_sf result op shift w_shift old_flags new_flags,
      `(w_shift = resize _ word_bits (resize _ 8 shift) ->
        result = shiftr _ op w_shift ->
        step_shr (OpShr (mk_pv tag1 op) (mk_pv tag2 shift) (IntValue result) mod_sf) old_flags new_flags)
  .
(**
## Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.
- flags, if `set_flags` modifier is set.

## Usage

- Operations with bit masks.
- Fast arithmetic.

## Similar instructions

- `shl`, `shr`, `rol` and `ror` are encoded as variants of the same instruction.
 *)
End Shr.
