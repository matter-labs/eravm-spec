Require Core PrimitiveValue MemoryBase.

Import Common Core MemoryBase BinInt PrimitiveValue.

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
