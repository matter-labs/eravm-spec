Require SemanticCommon.

Import Common CoreSet Modifiers SemanticCommon PrimitiveValue.

Section AndDefinition.
  Open Scope ZMod_scope.

  Generalizable Variables op tag.

  Inductive step_and: instruction -> flags_tsmallstep :=
  (**
# Bitwise AND

## Abstract Syntax

[%OpAnd         (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap) (flags:mod_set_flags)]

## Syntax

- `and in1, in2, out`
- `and.s in1, in2, out`, to set `swap` modifier.
- `and! in1, in2, out`, to set `set flags` modifier.
- `and.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

## Summary

Bitwise AND of two 256-bit numbers.

## Semantic

- result is computed as a bitwise AND of two operands.
- flags are computed as follows:
   - `EQ` is set if $result = 0$.
   - `OF_LT` and `GT` are cleared

Reminder: flags are only set if `set_flags` modifier is set.

## Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.
- flags, if `set_flags` modifier is set.

## Usage

- operations with bit masks

## Similar instructions

- `and`, `or` and `xor` are encoded as variants of the same [%mach_instruction].
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
