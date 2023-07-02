Require lib.ZMod Common Memory.

(** * Ergs *)
Section Ergs.
Import Common Memory ZMod ZArith.
Open Scope Z_scope.

Definition ergs_bits := 32%nat.
Definition ergs := int_mod ergs_bits.
Definition ergs_of := int_mod_of ergs_bits.
#[reversible]
Local Coercion ergs_of : Z >-> int_mod.

Definition VM_CYCLE_COST_IN_ERGS: Z := 4.
Definition RAM_PERMUTATION_COST_IN_ERGS: Z := 1.
Definition CODE_DECOMMITMENT_COST_PER_WORD_IN_ERGS: Z := 4.
Definition STORAGE_APPLICATION_COST_IN_ERGS: Z := 678.
Definition CODE_DECOMMITTER_SORTER_COST_IN_ERGS: Z := 1.
Definition LOG_DEMUXER_COST_IN_ERGS: Z := 1.
Definition STORAGE_SORTER_COST_IN_ERGS: Z := 2.
Definition EVENTS_OR_L1_MESSAGES_SORTER_COST_IN_ERGS: Z := 1.
Definition INITIAL_WRITES_PUBDATA_HASHER_COST_IN_ERGS: Z := 18.
Definition REPEATED_WRITES_PUBDATA_HASHER_COST_IN_ERGS: Z := 11.
Definition CODE_DECOMMITMENT_SORTER_COST_IN_ERGS: Z := 1.

Definition L1_MESSAGE_MIN_COST_IN_ERGS: Z := 156250.
Definition INITIAL_WRITES_PUBDATA_HASHER_MIN_COST_IN_ERGS: Z := 0.
Definition REPEATED_WRITES_PUBDATA_HASHER_MIN_COST_IN_ERGS: Z := 0.

Definition STORAGE_WRITE_HASHER_MIN_COST_IN_ERGS: Z := 0.

Definition KECCAK256_CIRCUIT_COST_IN_ERGS: Z := 40.
Definition SHA256_CIRCUIT_COST_IN_ERGS: Z := 7.
Definition ECRECOVER_CIRCUIT_COST_IN_ERGS: Z := 1112.

Definition INVALID_OPCODE_ERGS: Z := unsigned_max 32.

Definition RICH_ADDRESSING_OPCODE_ERGS: Z
  := VM_CYCLE_COST_IN_ERGS + 2 * RAM_PERMUTATION_COST_IN_ERGS.
Definition AVERAGE_OPCODE_ERGS: Z
  := VM_CYCLE_COST_IN_ERGS + RAM_PERMUTATION_COST_IN_ERGS.



Definition STORAGE_READ_IO_PRICE: Z := 150.
Definition STORAGE_WRITE_IO_PRICE: Z := 250.
Definition EVENT_IO_PRICE: Z := 25.
Definition L1_MESSAGE_IO_PRICE: Z := 100.
Definition CALL_LIKE_ERGS_COST: Z := 20.
Definition ERGS_PER_CODE_WORD_DECOMMITTMENT: Z := CODE_DECOMMITMENT_COST_PER_WORD_IN_ERGS.


Definition DECOMMITMENT_MSG_VALUE_SIMULATOR_OVERHEAD: Z := 64000.
Definition MSG_VALUE_SIMULATOR_ADDITIVE_COST: Z := 11500 + DECOMMITMENT_MSG_VALUE_SIMULATOR_OVERHEAD.
Definition MSG_VALUE_SIMULATOR_MIN_USED_ERGS: Z := 8000 + DECOMMITMENT_MSG_VALUE_SIMULATOR_OVERHEAD.

Definition MIN_STORAGE_WRITE_PRICE_FOR_REENTRANCY_PROTECTION: Z := Z.max
                                                                    (MSG_VALUE_SIMULATOR_ADDITIVE_COST - MSG_VALUE_SIMULATOR_MIN_USED_ERGS + 1)
                                                                    (2300 + 1).
Definition MIN_STORAGE_WRITE_COST: Z := Z.max
                                         MIN_STORAGE_WRITE_PRICE_FOR_REENTRANCY_PROTECTION
                                         STORAGE_WRITE_HASHER_MIN_COST_IN_ERGS.

Definition INITIAL_STORAGE_WRITE_PUBDATA_BYTES: Z := 64.
Definition REPEATED_STORAGE_WRITE_PUBDATA_BYTES: Z := 40.
Definition L1_MESSAGE_PUBDATA_BYTES: Z := (1 + 1 + 2 + 20 + 32 + 32).

Definition growth_cost (diff:mem_address) : ergs := diff.
End Ergs.
