Require Core PrimitiveValue MemoryBase lib.PMap_ext.

Import Bool Common Core MemoryBase BinInt List PrimitiveValue PMap_ext.
Import ListNotations.

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


Section Depot.
  (**
# Storage of a contract

A **storage** is a persistent linear mapping from $2^{256}$ addresses to words.

Therefore, given a storage, each word storage is addressed through a 256-bit
address.

In storage, individual bytes inside a word can not be addressed directly: a load
or a store happen on a word level.

Both word address in storage and word width are 256 bits.

All words in a storage are zero-initialized on genesis.
Therefore, reading storage word prior to writing yields zero. It is a
well-defined behavior. *)

  Definition storage_params := {|
                                addressable_block := word;
                                address_bits := 256;
                                default_value := word0;
                                writable := true
                              |}.

  Definition storage_address := BITS (address_bits storage_params).
  Definition storage: Type := mem_parameterized storage_params.

  (**  Storage start blanks. *)
  Definition storage_empty : storage := empty storage_params.

  (** Storage does not hold contract code, it is a responsibility of decommittment
processor [%decommitter].

Storage is a part of a [%shard], which is a part of [%depot].

One storage is selected as an active storage, it is the storage corresponding to
the [%current_shard] and [%current_contract].

Use the instruction [%OpSStore] to write to the active storage, [%OpSLoad] to
read from the active storage.

## Instructions

Instruction [%OpSLoad] implements reading from storage; instruction [%OpSStore]
implements writing to storage.

## Memory model

Storage has a sequentially-consistent, strong memory model.
All writes are atomic and immediately visible; reads are guaranteed to return
the last value written.


# Shards and contracts

A **contract** is uniquely identified by its 160-bit address [%contract_address].
In future, the address could be seamlessly extended to up to 256 bits.

A **shard** is a mapping of contract addresses to storages.

Therefore, every contract is associated with as many storages as there are
shards. *)

  Definition shard_params := {|
                              addressable_block := storage;
                              address_bits := 160;
                              default_value := storage_empty;
                              writable := true
                            |}.

  Definition contract_address := address shard_params.
  Definition contract_address_bits := address_bits shard_params.
  Definition shard := mem_parameterized shard_params.

  (** Contracts are also associated with code. The association is global per depot
and implemented by [%Decommitter]. Therefore, the contract code is the same for
all shards, but the storages of a contract in different shards differ.

Unlike in Ethereum, there is only type of accounts capable of both transacting
coins and executing contracts.

Contracts with addresses in range from 0 (inclusive) to [%KERNEL_MODE_MAXADDR]
(exclusive) are **system contracts**; they are allowed to execute all
instructions.

# Depot

**Depot** is a collection of shards.
Depot is the global storage of storages of all contracts.

   *)
  Definition depot_params :=
    {|
      addressable_block := shard;
      address_bits := 8;
      default_value := empty _;
      writable := true
    |}.

  Definition depot := mem_parameterized depot_params.

  Definition shard_id := BITS (address_bits depot_params).
  (** There are currently two shards: one for zkRollup, one for zkPorter. *)

  Inductive shard_exists: shard_id -> Prop :=
  | se_rollup: shard_exists (fromZ 0)
  | se_porter: shard_exists (fromZ 1)
  .


  (** The **fully qualified address** of a word in depot is a triple:


$(\texttt{shard\_id}, \texttt{contract\_id} , \texttt{key})$

It is formalized by [%fqa_key].
   *)

  Record fqa_storage := mk_fqa_storage {
                            k_shard: shard_id;
                            k_contract: contract_address;
                          }.
  Record fqa_key := mk_fqa_key {
                        k_storage :> fqa_storage;
                        k_key: storage_address
                      }.

  Inductive storage_get (d: depot): fqa_storage -> storage -> Prop :=
  | sg_apply: forall storage shard s c st,
      shard_exists s ->
      MemoryBase.load_result depot_params s d shard ->
      MemoryBase.load_result shard_params c shard storage  ->
      storage_get d (mk_fqa_storage s c) st .

  Inductive storage_read (d: depot): fqa_key -> word -> Prop :=
  | sr_apply: forall storage sk c w,
      storage_get d sk storage ->
      storage_read d (mk_fqa_key sk c) w.

  Inductive storage_write (d: depot): fqa_key -> word -> depot -> Prop :=
  | sw_apply: forall storage shard sk s c k w  shard' depot' storage',
      storage_get d sk storage ->
      MemoryBase.store_result storage_params k storage w storage' ->
      MemoryBase.store_result shard_params c shard storage' shard'  ->
      MemoryBase.store_result depot_params s d shard' depot' ->
      storage_write d (mk_fqa_key sk k) w depot'.

End Depot.

Section Memory.

  Section Pages.
    (** # Main memory (transient)
## Memory structure

Contract execution routinely uses **main memory** to hold instructions, stack,
heaps, and constants.

When the execution of a contract starts, new pages are allocated for:

- contract code: [%code_page], fetched by decommitter; see [%Decommitter] and
  [%FarCallDefinitions]);
- data stack: [%stack_page];
- heap: [%data_page];
- aux_heap: [%data_page];
- constants: [%const_page], implementation may chose to allocate code and
  constants on the same page.

Therefore, the types of pages are: data pages, stack pages, constant data pages,
and code pages. **)

    Context {code_page const_page data_page stack_page: Type}.

    Inductive page_type :=
    | DataPage : data_page -> page_type
    | StackPage : stack_page -> page_type
    | ConstPage : const_page -> page_type
    | CodePage : code_page -> page_type
    .

    Record page := mk_page {
                       type:> page_type
                     }.
    (** **Memory** is a collection of pages [%memory], each page is attributed a
    unique identifier [%page_id]. Pages persist for as long as they can be read
    by some code; in presence of [%FatPointer] the page lifetime may exceed the
    lifetime of the frame that created it. *)

    Definition page_id := nat.
    Definition pages := list (page_id * page).
    Record memory := mk_pages {
                         mem_pages:> pages;
                       }.

    Inductive page_has_id : memory -> page_id -> page -> Prop :=
    | mpid_select : forall mm id page,
        List.In (id, page) mm ->
        page_has_id (mk_pages mm) id page.

    (** The set of identifiers has a complete linear order, ordering the pages
    by the time of creation. The ability to distinguish older pages from newer
    is necessary to prevent returning fat pointers to pages from older frames.
    See e.g. [% step_RetExt_ForwardFatPointer]. *)
    Section Order.
      Definition page_ordering := Nat.leb.
      Definition page_eq x y := page_ordering x y && page_ordering y x.
      Definition page_neq x y := negb (page_eq x y).
      Definition page_older (id1 id2: page_id) : bool :=
        page_ordering id1 id2.
    End Order.

    (** Predicate [%page_replace] describes a relation between two memories
    [%m1] and [%m2], where [%m2] is a copy of [%m1] but a page with it [%id] is
    replaced
    by another page [%p].*)
    Inductive page_replace_list (id:page_id) (p:page): pages -> pages -> Prop :=
    | mm_replace_base: forall oldpage newpage tail,
        page_replace_list id p ((id, oldpage)::tail) ((id,newpage)::tail)
    | mm_replace_ind: forall oldpage not_id tail tail',
        page_replace_list id p tail tail' ->
        id <> not_id ->
        page_replace_list id p ((not_id,oldpage)::tail) ((not_id,oldpage)::tail').

    Inductive page_replace (id:page_id) (p:page): memory -> memory -> Prop :=
    | prl_apply: forall ls ls',
        page_replace_list id p ls ls' ->
        page_replace id p (mk_pages ls) (mk_pages ls').

    (** Function [%page_alloc] creates a new page in memory. *)
    Definition page_alloc (p:page) (m: memory) : memory :=
      let new_id := length (mem_pages m) in
      match m with
      | mk_pages mem_pages => mk_pages (cons (new_id, p) mem_pages)
      end.

  End Pages.


  (** ### Data pages

A **data page** contains individually addressable bytes. Each data page holds
$2^{32}$ bytes. *)

  Definition data_page_params := {|
                                  addressable_block := u8;
                                  address_bits := 32;
                                  default_value := zero8;
                                  writable := true
                                |}.
  Definition mem_address := address data_page_params.
  Definition mem_address_zero: mem_address := zero32.
  Definition mem_address_bits := data_page_params.(address_bits).

  Definition data_page := mem_parameterized data_page_params.

  (** There are currently two types of data pages:

- [%Heap]
- [%AuxHeap].

  We call both of them **heap variants** for brevity, as in almost all cases
  they are handled in a similar way. *)
  Inductive data_page_type := Heap | AuxHeap.
  Definition page_bound := prod data_page_type mem_address.

  Open Scope ZMod_scope.
  Definition growth (current_bound: mem_address) (query_bound: mem_address)
    : mem_address :=
    if query_bound < current_bound then zero32 else
      snd (query_bound - current_bound).
  (**

Note: only selected few instructions can access data pages:

- [%OpLoad]/[%OpLoadInc]
- [%OpStore]/[%OpStoreInc]
- [%OpLoadPointer]/[%OpLoadPointerInc]

Every byte on data pages has an address, but these instructions read or store 32-byte words.

-----

Fat pointers [%fat_ptr] define slices of data pages and allow passing them
between contracts.

### Stack pages

A **stack page** contains $2^{16}$ primitive values (see [%primitive_value]).
Reminder: primitive values are tagged words.

   *)
  Definition stack_page_params := {|
                                   addressable_block := primitive_value;
                                   address_bits := 16;
                                   default_value := mk_pv false word0;
                                   writable := true
                                 |}.

  Definition stack_address := address stack_page_params.
  Definition stack_address_bits := stack_page_params.(address_bits).
  Definition stack_address_zero: stack_address := zero16.

  Definition stack_page := mem_parameterized stack_page_params.

  (** #### Data stack in EraVM

There are two stacks in EraVM: call stack to support the execution of functions
and contracts, and data stack to facilitate computations. This section details
the data stack.

At each moment of execution, one stack page is active; it is associated with the
topmost of external frames, which belongs to the contract currently being
executed. See [%active_extframe], its field [%ecf_mem_ctx] and subfield
[%ctx_stack_page_id].

Each contract instance has an independent stack on a separate page.
Instead of zero, stack pointer on new stack pages start with a value
[%INITIAL_SP_ON_FAR_CALL]. Stack addresses in range [0; [%INITIAL_SP_ON_FAR_CALL]) can be used as a scratch space.

Topmost frame of the callstack, whether internal or external, contains the stack
pointer (SP) value [%cf_sp]; which points to the address after the topmost element of
the stack. That means that the topmost element of the stack is located in word
number $(\mathit{SP}-1)$ on the associated stack page.

Data stack grows towards greater addresses.
In other words, pushing to stack increases stack pointer value, and popping
elements decreases stack pointer.

### Const pages

A **const page** contains $2^{16}$ non tagged [%word]s.
They are not writable.

Implementation may put constants and code on the same pages.
In this case, the bytes on the same virtual page can be addressed in two ways:

- For instructions [%OpJump] and [%OpNearCall], the code addressing will be
  used: consecutive addresses correspond to 8-bytes instructions.
- For instructions like [%OpAdd] with [%CodeAddr] addressing mode, the const
  data addressing will be used: consecutive addresses correspond to 32-bytes
  words.

For example, [%OpJump 0], [%OpJump 1], [%OpJump 2], [%OpJump 3] will refer to
the first four instructions on the page; their binary representations, put
together, can be fetched by addressing the const page's 0-th word e.g.
[%OpAdd (CodeAddr R0 zero_16 ) (Reg R0) (Reg R1)].
   *)
  Definition const_address_bits := 16.

  Definition const_page_params := {|
                                   addressable_block := word;
                                   address_bits := const_address_bits;
                                   default_value := word0;
                                   writable := false
                                 |}.
  Definition const_address :=  address const_page_params.
  Definition const_page := mem_parameterized const_page_params.

  (** ### Code pages

A **code page** contains $2^{16}$ instructions.
They are not writable.

On genesis, code pages are filled as follows:

- The contract code is places starting from the address 0.
- The rest is filled with a value guaranteed to decode as [%invalid] instruction.

Const pages can coincide with code pages. *)

  Context {ins_type: Type} (invalid_ins: ins_type).

  (* Implementation note: [%code_address] should be [%address code_page_params] but we don't want to introduce
      dependency between code_address and instruction type *)
  Definition code_address_bits := 16.
  Definition code_address := BITS code_address_bits.
  Definition code_address_zero: stack_address := zero16.

  Definition code_page_params := {|
                                  addressable_block := ins_type;
                                  address_bits := code_address_bits;
                                  default_value := invalid_ins;
                                  writable := false
                                |}.
  Record code_page := mk_code_page {
                          cp_insns:> mem_parameterized code_page_params;
                        }.
  Definition code_length := code_address.

End Memory.

(** The definition [%vm_page] collects the specific types of pages used by
EraVM semantic. *)
#[global]
  Canonical vm_page {instr} (inv:instr) type : page := @mk_page (code_page inv) const_page data_page stack_page type.
#[global]
  Canonical vm_mem {instr} (inv:instr) type : memory := @mk_pages (code_page inv) const_page data_page stack_page type.
