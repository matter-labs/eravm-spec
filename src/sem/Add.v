Require SemanticCommon.

Import Bool Common Flags CoreSet Memory Modifiers State ZMod
  PrimitiveValue SemanticCommon.

Section Def.
  Open Scope ZMod_scope.

  Generalizable Variables op tag.

  Inductive step_add: instruction -> flags_tsmallstep :=
  (**
# Add

## Abstract Syntax

[%OpAdd (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)]

## Syntax

- `add in1, in2, out`
- `add.s in1, in2, out`, to set `swap` modifier.
- `add! in1, in2, out`, to set `set flags` modifier.
- `add.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

## Summary

Unsigned overflowing addition of two numbers modulo $2^{256}$.

## Semantic

- result is computed by unsigned addition of two numbers with overflow modulo $2^{256}$.

   $$result := op_1 + op_2 \mod 2^{256}$$

- flags are computed as follows:
   - `LT_OF` is set if overflow occurs, i.e. $op_1 + op_2 \geq 2^{256}$
   - `EQ` is set if $result = 0$.
   - `GT` is set if $op_1 \gt op_2$. An equivalent condition is: both `LT_OF` and `EQ` are cleared.

Reminder: flags are only set if `set_flags` modifier is set.

## Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.
- flags, if `set_flags` modifier is set.

## Usage

- Arithmetic operations.
- There is no dedicated `mov` instruction, so `add` is used to copy values around. Copying A to B is implemented as `add A, r0, B`.

## Similar instructions

Flags are computed exactly as in `sub`, but the meaning of overflow is different for addition and subtraction.

   *)
  | step_Add:
    forall mod_sf old_flags new_flags,
      `(
          let (result, new_OF) := op1 + op2 in
          let new_EQ := result == zero256 in
          let new_GT := negb new_EQ && negb new_OF in

          new_flags = apply_set_flags mod_sf
                        old_flags
                        (bflags new_OF new_EQ new_GT) ->

          step_add (OpAdd (mk_pv tag1 op1) (mk_pv tag2 op2) (IntValue result) mod_sf) old_flags new_flags)
  .
  Generalizable No Variables.

End Def.
