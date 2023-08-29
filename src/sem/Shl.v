Require sem.SemanticCommon.
Import Arith Core isa.CoreSet PrimitiveValue SemanticCommon spec.

Section ShlDefinition.
  Open Scope ZMod_scope.
  Generalizable Variables tag.
  Import operations operations.BitsNotations.
  Inductive step_shl: instruction -> flags_tsmallstep :=

  (**
# Shl

## Abstract Syntax

[%OpShl (in1: in_any) (in2: in_reg) (out: out_any) (swap:mod_swap) (flags:mod_set_flags)]

## Syntax

- `shl in1, in2, out`
- `shl.s in1, in2, out`, to set `swap` modifier.
- `shl! in1, in2, out`, to set `set flags` modifier.
- `shl.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

## Summary

Bitwise left shift of `in1` by the number of binary digits specified by the
lowest byte of `in2`. New binary digits (least significant bits in `out`) are
zeros.

## Semantic

Follows the scheme described in [%binop_state_bitwise_effect_spec].

- result is computed as `in1 << (in2 mod 256)`
- flags are computed as follows:
   - `EQ` is set if $result = 0$.
   - other flags are reset

Reminder: flags are only set if `set_flags` modifier is set. *)
  | step_Shl:
    forall mod_sf result op shift w_shift old_flags new_flags,
      `(shift = toNat (low 8 w_shift) ->
        result = shlBn op shift ->
        step_shl (OpShl (mk_pv tag1 op) (mk_pv tag2 w_shift) (IntValue result) mod_sf) old_flags new_flags)
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
End ShlDefinition.
