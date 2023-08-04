Require Flags.

Import Flags.

Section Modifiers.

  Inductive mod_swap := Swap | NoSwap.

  Definition apply_swap {T} (md: mod_swap) (a b:T) : T*T :=
    match md with
    | NoSwap => (a,b)
    | Swap => (b,a)
    end.

  Inductive mod_set_flags := SetFlags | PreserveFlags.

  Definition apply_set_flags (md: mod_set_flags) (f f':flags_state) : flags_state :=
    match md with
    | SetFlags => f'
    | PreserveFlags => f
    end.

End Modifiers.
