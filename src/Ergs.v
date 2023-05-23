Require lib.ZMod Common Memory.

(** * Ergs *)
Section Ergs.
Import Common Memory ZMod ZArith.
Open Scope Z_scope.

Definition ergs := u32.
#[reversible]
Local Coercion int_mod_of : Z >-> int_mod.

Definition VM_CYCLE_COST_IN_ERGS: ergs := 4.
Definition RAM_PERMUTATION_COST_IN_ERGS: ergs := 1.
Definition CODE_DECOMMITMENT_COST_PER_WORD_IN_ERGS: ergs := 4.
Definition STORAGE_APPLICATION_COST_IN_ERGS: ergs := 678.
Definition CODE_DECOMMITTER_SORTER_COST_IN_ERGS: ergs := 1.
Definition LOG_DEMUXER_COST_IN_ERGS: ergs := 1.
Definition STORAGE_SORTER_COST_IN_ERGS: ergs := 2.
Definition EVENTS_OR_L1_MESSAGES_SORTER_COST_IN_ERGS: ergs := 1.
Definition INITIAL_WRITES_PUBDATA_HASHER_COST_IN_ERGS: ergs := 18.
Definition REPEATED_WRITES_PUBDATA_HASHER_COST_IN_ERGS: ergs := 11.
Definition CODE_DECOMMITMENT_SORTER_COST_IN_ERGS: ergs := 1.

Definition L1_MESSAGE_MIN_COST_IN_ERGS: ergs := 156250.
Definition INITIAL_WRITES_PUBDATA_HASHER_MIN_COST_IN_ERGS: ergs := 0.
Definition REPEATED_WRITES_PUBDATA_HASHER_MIN_COST_IN_ERGS: ergs := 0.

Definition STORAGE_WRITE_HASHER_MIN_COST_IN_ERGS: ergs := 0.

Definition KECCAK256_CIRCUIT_COST_IN_ERGS: ergs := 40.
Definition SHA256_CIRCUIT_COST_IN_ERGS: ergs := 7.
Definition ECRECOVER_CIRCUIT_COST_IN_ERGS: ergs := 1112.

Definition INVALID_OPCODE_ERGS: ergs := unsigned_max 32.

Definition RICH_ADDRESSING_OPCODE_ERGS: ergs
  := (VM_CYCLE_COST_IN_ERGS.(int_val _) + 2 * RAM_PERMUTATION_COST_IN_ERGS.(int_val _)).
Definition AVERAGE_OPCODE_ERGS: ergs
  := (VM_CYCLE_COST_IN_ERGS.(int_val _)
                    + RAM_PERMUTATION_COST_IN_ERGS.(int_val _)).



Definition STORAGE_READ_IO_PRICE: ergs := 150.
Definition STORAGE_WRITE_IO_PRICE: ergs := 250.
Definition EVENT_IO_PRICE: ergs := 25.
Definition L1_MESSAGE_IO_PRICE: ergs := 100.
Definition CALL_LIKE_ERGS_COST: ergs := 20.
Definition ERGS_PER_CODE_WORD_DECOMMITTMENT: ergs := CODE_DECOMMITMENT_COST_PER_WORD_IN_ERGS.

Definition growth_cost (diff:mem_address) : ergs := diff.
End Ergs.
