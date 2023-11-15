Require PrimitiveValue memory.Pages memory.PageTypes Pointer.
Import PrimitiveValue memory.Pages memory.PageTypes Pointer.

Export memory.Pages memory.PageTypes.

(** # Informal overview

All memory available to the contract code can be divided into transient and
persistent memory.

- **Transient memory** exists to enable computations and does not persist between
  VM, like the main memory of personal computers.
- **Persistent memory** exists as a storage of untagged 256-bit [%word]s shared
  between the network participants.

Contract code uses transient memory to perform computations and uses the storage
to publish its results


## Persistent memory

The global persistent data structure is the [%depot]. It holds untagged 256-bit
words.

Depot is split in two [%shard]s: one corresponds to rollup, another to porter
(see [%shard_exists]).

Each shard is a map from a [%contract_address] (160 bit, might be extended in
future to up to 256 bits) to contract [%storage].

Each contract [%storage] is a linear mapping from $2^{256}$ **keys** to 256-bit
untagged words.

To address a word in any contract's storage, it is sufficient to know:

- shard
- contract address
- key

See [%fqa_key].

Contract has one independent storage per shard.

One shard is selected as currently active in [%state].

Contract code is global and shared between shards.

## Transient memory

Transient memory consists of **pages** ([%page_type]) holding data or code.
Each page holds $2^{32}$ bytes; all bytes are initialized to zero at genesis.

New pages are allocated implicitly when the contract execution starts; calling
another contract allocates more pages.
Pages persist for as long as they are referenced from the live code.

Pages hold one of:

- data: $2^{32}$ byte-addressable data for heap or auxheap; bounded, so reading or
  writing outside bounds leads to a paid growth of available portion.
- code: instruction-addressable, read-only;
- constants: $2^{16}$ word-addressable, read-only;
- stack: $2^{16}$ words, word-addressable, tagged words. When the execution of a
  contract starts, the initial value of stack pointer is
  [%INITIAL_SP_ON_FAR_CALL].


The following describes all types of memory formally and with greater detail.
 *)

(** The definition [%vm_page] collects the specific types of pages used by
 EraVM semantic. *)

Definition stack_address := stack_address pv0.
Definition stack_address_bits := stack_address_bits pv0.
Definition stack_page := stack_page pv0.
Definition stack_page_params := stack_page_params pv0.

#[global]
  Canonical vm_page {instr} (inv:instr) type : page := @mk_page (code_page inv) const_page data_page stack_page type.
#[global]
  Canonical vm_mem {instr} (inv:instr) type : memory := @mk_pages (code_page inv) const_page data_page stack_page type.
