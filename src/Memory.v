From RecordUpdate Require Import RecordSet.
Require Core PrimitiveValue MemoryBase lib.PMap_ext.
Import Common Core MemoryBase BinInt List PrimitiveValue PMap_ext.
Import ListNotations.
Import RecordSetNotations.


(** # Storage

A **storage** is a linear mapping from $2^{256}$ addresses to words.

Therefore, each word is addressed through a  256-bit address.

In storage, individual bytes inside a cell can not be addressed directly: one load or store happen on a cell level.

Both word address in storage and cell width are 256 bits; it is a
meaningless coincidence.

All words in a storage are zero-initialized on genesis.
Therefore, reading storage cell prior to writing is defined to return zero.

*)

Definition storage_params := {|
                              addressable_block := word;
                              address_bits := 256;
                              default_value := word0;
                              writable := true
                            |}.

Definition storage_address := ZMod.int_mod (address_bits storage_params).
Definition storage: Type := mem_parameterized storage_params.

(**  Storage start blanks. *)
Definition storage_empty : storage := empty storage_params.

(**
Storage does not hold contract code, it is a responsibility of decommittment processor.

Storage is a part of a shard, which is a part of depot.

## Instructions

Instruction [OpSLoad] implements reading from storage; instruction [OpSWrite] implements writing to storage.
    

## Memory model

Storage has a sequentially-consistent, strong mem model. All writes 
are atomic and immediately visible; reads are guaranteed to return the last value written.


# Shards and contracts

A **contract** is uniquely identified by its 160-bit address.
In future, the address could be seemlessly extended to up to 256 bits.


A **shard** is a mapping of contract addresses to storages.

Therefore, every contract is associated with as many storages as there are shards.
*)

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
and implemented with [Decommitter]. Therefore, the code is the same for all
shards, but the storages of a contract in different shards differ.

Contracts with addresses in range from 0 (inclusive) to [KERNEL_MODE_MAXADDR] (exclusive) are **system contracts**; they are allowed to execute all instructions.

 *)
Definition KERNEL_MODE_MAXADDR_LIMIT : contract_address := ZMod.int_mod_of _ (2^16).

Definition addr_is_kernel (addr:contract_address) : bool := ZMod.lt_unsigned _ addr KERNEL_MODE_MAXADDR_LIMIT.

(** # Depot

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

Definition shard_id := ZMod.int_mod (address_bits depot_params).
(** There are currently two shards: one for zkRollup, one for zkPorter. *)

Inductive shard_exists: shard_id -> Prop :=
| se_rollup: shard_exists (ZMod.int_mod_of _ 0%Z)
| se_porter: shard_exists (ZMod.int_mod_of _ 1%Z)
.


Section Memory.

(** # Memory *)
  Section Pages.
    Import Bool.
    (** ## Memory structure
        
Contract execution routinely uses **main memory** to hold instructions, stack, heaps, and constants.

When the execution of a contract starts, new pages are allocated for:

- contract code: [code_page], fetched by decommitter; see [Decommitter])
- data stack: [stack_page]
- heap: [data_page]
- aux_heap: [data_page]
- constants: [const_page], implementation may chose to allocate code and constants on the same page.
 
Therefore, the types of pages are: data pages, stack pages, constant data pages, and code pages. **)

    Record pages_config := {
        pc_code: Type; 
        pc_const: Type; 
        pc_data: Type; 
        pc_stack: Type;
      }.
    
    Context {config: pages_config}
        (code_page  := pc_code config)
        (const_page := pc_const config)
        (data_page  := pc_data config)
        (stack_page := pc_stack config).
    
    Inductive page :=
    | DataPage : data_page -> page
    | StackPage : stack_page -> page
    | ConstPage : const_page -> page
    | CodePage : code_page -> page.

    
    (** **Main memory** is a collection of pages with unique identifiers. *)

    Definition page_id := nat.
    Definition memory := list (page_id * page).

    (** There are no guarantees about the page identifier values or type;
    however, it is required to be able to distinguish older pages from newer. *)
    Definition page_ordering := Nat.leb.

    Definition page_eq x y := page_ordering x y && page_ordering y x.
    Definition page_neq x y := negb (page_eq x y).
    
    
    Definition page_older (id1 id2: page_id) : bool :=
      page_ordering id1 id2.
    
    (**
Pages persist for as long as they can be read by some code; in presence of [FatPointer] the page lifetime may exceed the lifetime of the frame that created it.
     *)
    Inductive page_has_id : memory -> page_id -> page -> Prop :=
    | mpid_select : forall mm id page,
        List.In (id, page) mm ->
        page_has_id mm id page.

    Inductive page_replace:  page_id -> page -> memory -> memory -> Prop :=
    | mm_replace_base: forall oldpage id newpage tail,
        page_replace id newpage ((id, oldpage)::tail) ((id,newpage)::tail)
    | mm_replace_ind: forall oldpage id not_id newpage tail tail',
        page_replace id newpage tail tail' ->
        id <> not_id ->
        page_replace id newpage ((not_id,oldpage)::tail) ((not_id,oldpage)::tail').


    Definition page_alloc (p:page) (m: memory ) : memory :=
      let new_id := length m in
      cons (new_id, p) m.
  End Pages.


(**
### Data pages

A **data page** contains individually addressable bytes. Each data page holds $2^{32}$ bytes.

*)
  

  Definition data_page_params := {|
                                  addressable_block := u8;
                                  address_bits := 32;
                                  default_value := zero8;
                                  writable := true
                                |}.
  Definition mem_address := address data_page_params.
  Definition mem_address_zero: mem_address := zero32.

  Definition data_page := mem_parameterized data_page_params.

  (** There are currently two types of data pages: [Heap] and [AuxHeap] pages. *)
  Inductive data_page_type := Heap | AuxHeap.


(** Note: only instructions from UMA (unaligned memory access) instruction family can access data pages ([OpLoad]/[OpLoadInc], [OpStore]/[OpStoreInc], [OpLoadPointer]/OpLoadPointerInc]).
Every byte on data pages has an address, but the instructions from UMA family read or store 32-byte words.

### Stack pages

A **stack page** contains $2^{16}$ primitive values (see [primitive_value]).
*)
  Definition stack_page_params := {|
                                   addressable_block := primitive_value;
                                   address_bits := 16;
                                   default_value := mk_pv false word0;
                                   writable := true
                                 |}.

  Definition stack_address := address stack_page_params.
  Definition stack_address_zero: stack_address := zero16.

  Definition stack_page := mem_parameterized stack_page_params.


(** ### Const pages

A **const page** contains $2^{16}$ primitive values (see [primitive_value]).
They are not writable.

Const pages can coincide with code pages.
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

Each **code page** contains $2^{16}$ instructions.
They are not writable.

Const pages can coincide with code pages.

Default value is invalid instruction [invalid_ins].
 *)
  
  Context {ins_type: Type} (invalid_ins: ins_type).

  (* should be [address code_page_params] but we don't want to introduce
      dependency between code_address and instruction type *)
  Definition code_address_bits := 16.
  Definition code_address :=  ZMod.int_mod code_address_bits.
  Definition code_address_zero: stack_address := zero16.
  
  Definition code_page_params := {|
                                  addressable_block := ins_type;
                                  address_bits := code_address_bits;
                                  default_value := invalid_ins;
                                  writable := false
                                |}.
  Definition code_page := mem_parameterized code_page_params.
  Definition code_length := code_address.


End Memory.

Definition era_pages {instr} {inv:instr}:= Build_pages_config (code_page inv) const_page data_page stack_page.
