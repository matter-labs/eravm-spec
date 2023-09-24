Require Flags.
Import Flags.

Section Modifiers.

  (** # Instruction modifiers

There are two modifiers common between multiple [%asm_instruction]: `swap` and `set_flags`.

## Swap modifier

This modifier, when applied, swaps two input operands.
Definition [%asm_instruction] shows which instructions support it.

Input operands usually have different addressing modes, e.g. the divisor in
[%Assembly.OpDiv] may be only fetched from registers, not memory. Applying
`swap` modifier allows to fetch rather the divisor from memory, and the divident
can be fetched from register.

The function [%to_core] transforms [%asm_instruction] into a core [%instruction] and applies the `swap` modifier.

   *)
  Inductive mod_swap := Swap | NoSwap.

  Definition apply_swap {T} (md: mod_swap) (a b:T) : T*T :=
    match md with
    | NoSwap => (a,b)
    | Swap => (b,a)
    end.

  (** ## Set flags

Only instructions *with the modifier [%mod_set_flags] set* may change the state
of flags in [%gs_flags].
Therefore, if [%mod_set_flags] is not set, it is guaranteed that the instruction
will not change the flags state.
   *)
  Inductive mod_set_flags := SetFlags | PreserveFlags.

  (** If set flags modifier [%md] is set, preserve the old flags state [%f];
otherwise, return the new state [%f']. *)
  Definition apply_set_flags (md: mod_set_flags) (f f':flags_state) : flags_state :=
    match md with
    | SetFlags => f'
    | PreserveFlags => f
    end.

End Modifiers.
