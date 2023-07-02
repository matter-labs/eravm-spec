Require Core Memory .
Import Core Memory.

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

