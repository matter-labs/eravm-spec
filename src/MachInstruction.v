Require  Predication.

Import Flags Predication.

(**
# Structure of machine instructions

## Inner structure

This section presents a high-level description of how to construct a valid instruction.

§1. Instructions have a part common to all instructions, and an instruction-specific part.

§1.1. The common part [instruction] consists of:

- Opcode: encodes instruction type. See [opcode_specific].
- Common modifiers: alters the meaning of instruction. See [common_mod], [ins_mods].

  1. `swap`: if an instruction has two input operands, this modifier swaps
    them.

*)
Inductive mod_swap := Swap | NoSwap.

Definition apply_swap {T} (md: mod_swap) (a b:T) : T*T :=
  match md with
  | NoSwap => (a,b)
  | Swap => (b,a)
  end.

(**
  For example, if `sub in1, in2, out1` computes `in1`-`in2`, `sub` with
  `swap` modifier computes `in2` - `in1`. This is useful because `in1` has
  richer address modes: it can be e.g. fetched from stack, whereas `in2` can
  only be fetched from a register.


  2. `set_flags`: if set, instruction is allowed to change the flags. If
    cleared, the instruction will not touch the flags.
 *)
Inductive mod_set_flags := SetFlags | PreserveFlags.

Definition apply_set_flags (md: mod_set_flags) (f f':flags_state) : flags_state :=
  match md with
  | SetFlags => f'
  | PreserveFlags => f
  end.

(**

 - Predication of execution: instruction is executed only if the currently set
flags are compatible with the condition. Each instruction has a condition
encoded inside it. See [flags_activated], [ins_mods], [global_state], [gs_flags].


§1.2. Additionally, depending on [opcode_specific], an instruction may have:

- Exclusive modifiers: alter the meaning of instruction, e.g. [binop_mod].
- Operands: up to two input operands `in1` and `in2`, and up to two output operands `out1` and `out2`. Their allowed formats are systematized in the section Addressing Modes.

 *)


Record common_mod : Set := mk_cmod {
                               cm_swap: mod_swap;
                               cm_set_flags: mod_set_flags
                             }.
