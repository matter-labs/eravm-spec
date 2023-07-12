Require Common lib.ZMod.

Import ZMod Common ZArith.
Section Parameters.
  Open Scope ZMod_scope.


  (**

# EraVM architecture overview


EraVM is a 256-bit register-based language machine with two stacks, and dedicated memory for code, data, stack and constants.
   *)
  Definition word_bits: nat := 256.

  Definition word: Set := int_mod word_bits.
  (** [%word0] is a word with a zero value. *)
  Definition word0: word := int_mod_of word_bits 0%Z.
  Import Nat.
  Definition bytes_in_word : nat := word_bits/bits_in_byte.
  Definition z_bytes_in_word : Z := Z.of_nat bytes_in_word.
End Parameters.
  (**
![](img/arch-overview.png)


- **Memory**, provides access to transient memory, consisting of pages. See [%Memory].
- **Storage**, provides access to persistent storage with two shards, each shard maps $2^{160}$ contracts, to a key-value storage.   See [%Memory].
- **EventSink**, collects events and L2→L1 messages. See [%Events].
- **Precompile processor** executes precompiles e.g. `keccak256`, `sha256`, and so on. See [%Precompiles].
- **Decommittement processor**, stores and decommits the code of contracts. See [%Decommitter].

## Functions and contracts

In EraVM, contracts are the coarse-grained execution units.
Contracts may have multiple **functions** in them; a contract may execute its
functions by using **near call** instruction [%OpNearCall].
A contract may also call other contracts by using **far call** instructions
[%OpFarCall], [%OpMimicCall], or [%OpDelegateCall].

By **running instance** of a function or a contract we mean a piece of VM runtime
state associated with the current execution of a function or a contract, as
described by [%callstack].

EraVM allows recursive execution of functions and contracts.
For example, a contract $A$ calls a function $f_1$ which calls a function $f_2$
which calls a contract $B$, which calls a function $g_1$
...
During the execution of $g_1$, **running instances** of $A$, $f_1$, $f_2$ keep
existing, waiting for the control to return to them.

Recursive execution is also allowed, so a contract $C$ may call itself directly,
or call either functions or other contracts, which may call $C$ again.

Launching a contract allocates memory pages dedicated to it (see
[%alloc_pages_extframe]).
In a running instance of a contract, this contract's functions share these
memory pages.

Contracts have more contract-specific state associated to them than functions.
However, running instances of both functions and contracts have their own
balance in ergs, exception handlers, program counter and stack pointer values.

## Execution state

EraVM's functionality is to sequentially execute instructions.

The main components of EraVM's execution state are:

- 256-bit tagged general-purpose registers R1--R15 and a reserved register R0
  holding a constant 0. See [%regs_state].
- Three flags: overflow/less-than, equals, greater-than. See
  [%flags_state].
- Data stack holding tagged words. It is located on a dedicated [%stack_page].
- Callstack, holding callframes, which contain such information as the program
  counter, data stack pointer, current ergs balance, current contract's address,
  and so on. See [%CallStack].
- Frames in callstack can be internal (belong to a function, near called) frames
  or external frames (belong to a contract, far called, richer state).
- Read-only pages for constants and code, one per contract stack frame.


## Instructions

Refer to the section [%Instructions] for the list of supported instructions.

All instructions are predicated; it means, that they contain an explicit
condition about the current flags state. If the condition is satisfied, they are
executed, otherwise they are skipped (but their basic cost is still paid). See
[%instruction_predicated].

Instruction can accept data and return results in various formats.

- The formats of instruction operands are described in [%Addressing].
- The address resolution to locations in memory is described in [%resolve]
- Reading and writing to memory is described in [%MemoryOps].


## Modes
VM has two modes which can be independently turned on and off.

1. Kernel mode

  First [%KERNEL_MODE_MAXADDR_LIMIT] contracts are marked as system contracts.
  VM executes them in kernel mode, allowing an access to a richer instruction
  set, containing instructions potentially harmful to the global state e.g.
  [%OpContextIncrementTxNumber]. See [%KernelMode].

2. Static mode

   Intuitively, executing code in static mode aims at limiting its effects on
   the global state, similar to executing pure functions. Globally visible
   actions like emitting events or writing to storage are forbidden in static
   mode. See [%StaticMode].

## Ergs

Instructions and some other actions should be paid for with a resource called
**ergs**, similar to Ethereum's gas. See the overview in [%Ergs].

## Operation

Context of EraVM

When the server needs to build a new block, it starts an instance of EraVM.

EraVM accepts three parameters:

1. Bootloader's [%versioned_hash].
2. Default code hash [%DEFAULT_AA_VHASH].
3. A boolean flag `is_porter_available`, to determine the number of shards (two
   if zkPorter is available, one otherwise).

Bootloader is a contract written in YUL in charge of block construction. See
[%Bootloader].
*)



Definition timestamp := nat.
Definition tx_num := u16.
