Require SemanticCommon.

Import Common CoreSet Modifiers SemanticCommon PrimitiveValue.

Section OrDefinition.
  Open Scope ZMod_scope.

  Generalizable Variables op tag.

  Inductive step_or: instruction -> flags_tsmallstep :=
  (**
# Bitwise OR

## Abstract Syntax

[%OpOr          (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap) (flags:mod_set_flags)]

## Syntax

- `or in1, in2, out`
- `or.s in1, in2, out`, to set `swap` modifier.
- `or! in1, in2, out`, to set `set_flags` modifier.
- `or.s! in1, in2, out`, to set both `swap` and `set_flags` modifiers.

## Summary

Bitwise OR of two 256-bit numbers.

## Semantic

- result is computed as a bitwise OR of two operands.
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
