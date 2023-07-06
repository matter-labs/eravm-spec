Require Common lib.ZMod.

Import ZMod Common ZArith.
Section Parameters.
  Open Scope ZMod_scope.


  (**

# EraVM architecture overview


EraVM is a 256-bit register-based language machine with stack, dedicated memory for code, data, stack and constants.
   *)
  Definition word_bits: nat := 256.

  Definition word: Set := int_mod word_bits.
  (**
![](img/arch-overview.png)


- **Memory**, provides access to transient memory, consisting of pages. See [%Memory].
- **Storage**, provides access to persistent storage with two shards, each shard maps $2^{160}$ contracts, to a key-value storage. See [%Memory] and [%Storage].
- **EventSink**, collects events and L2→L1 messages. See [%Events].
- **Precompile processor** executes precompiles e.g. `keccak256`, `sha256`, and so on. See [%Precompiles].
- **Decommittement processor**, stores and decommits the code of contracts. See [%Decommitter].


## Execution state

EraVM's functionality is to sequentially execute instructions.

The main components of EraVM's execution state are:

- 256-bit tagged general-purpose registers R1--R15 and a reserved register R0 holding a constant 0. See [%GPR.regs_state].
- Three flags: overflow/less-than, equals, greater-than. See [%Condition.flags_state].
- Callstack, holding callframes, which include program counter, stack pointer, current ergs balance, current contract's address, and so on. See [%CallStack].
- Stack holding tagged words.
- Read-only pages for constants and code, one per contract stack frame.

First contracts are marked as system, so VM executes them in kernel mode, allowing an access to a richer instruction set. See [%KernelMode].


Instructions and some other actions should be paid for with **ergs**, an analogue of gas. See the overview in [%Ergs].

All instructions contain an encoded execution condition. It means that before executing any instruction flags are checked, and if they do not match the required condition, the instruction is skipped.



   *)


  (** [%word0] is a word with a zero value. *)
  Definition word0: word := int_mod_of word_bits 0%Z.
  Import Nat.
  Definition bytes_in_word : nat := word_bits/bits_in_byte.
  Definition z_bytes_in_word : Z := Z.of_nat bytes_in_word.
End Parameters.


Definition timestamp := nat.
Definition tx_num := u16.
