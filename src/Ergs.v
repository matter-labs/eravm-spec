Require lib.ZMod Common.

(** * Ergs *)
Section Ergs.
Import Common ZMod ZArith.
Open Scope Z_scope.

Definition VM_CYCLE_COST_IN_ERGS: u32 := int_mod_of 32 4%Z.
Definition RAM_PERMUTATION_COST_IN_ERGS: u32 := int_mod_of 32 1%Z.
Definition CODE_DECOMMITMENT_COST_PER_WORD_IN_ERGS: u32 := int_mod_of 32 4%Z.
Definition STORAGE_APPLICATION_COST_IN_ERGS: u32 := int_mod_of 32 678%Z.
Definition CODE_DECOMMITTER_SORTER_COST_IN_ERGS: u32 := int_mod_of 32 1%Z.
Definition LOG_DEMUXER_COST_IN_ERGS: u32 := int_mod_of 32 1%Z.
Definition STORAGE_SORTER_COST_IN_ERGS: u32 := int_mod_of 32 2%Z.
Definition EVENTS_OR_L1_MESSAGES_SORTER_COST_IN_ERGS: u32 := int_mod_of 32 1%Z.
Definition INITIAL_WRITES_PUBDATA_HASHER_COST_IN_ERGS: u32 := int_mod_of 32 18%Z.
Definition REPEATED_WRITES_PUBDATA_HASHER_COST_IN_ERGS: u32 := int_mod_of 32 11%Z.
Definition CODE_DECOMMITMENT_SORTER_COST_IN_ERGS: u32 := int_mod_of 32 1%Z.

Definition L1_MESSAGE_MIN_COST_IN_ERGS: u32 := int_mod_of 32 156250%Z.
Definition INITIAL_WRITES_PUBDATA_HASHER_MIN_COST_IN_ERGS: u32 := int_mod_of 32 0%Z.
Definition REPEATED_WRITES_PUBDATA_HASHER_MIN_COST_IN_ERGS: u32 := int_mod_of 32 0%Z.

Definition STORAGE_WRITE_HASHER_MIN_COST_IN_ERGS: u32 := int_mod_of 32 0%Z.

Definition KECCAK256_CIRCUIT_COST_IN_ERGS: u32 := int_mod_of 32 40%Z.
Definition SHA256_CIRCUIT_COST_IN_ERGS: u32 := int_mod_of 32 7%Z.
Definition ECRECOVER_CIRCUIT_COST_IN_ERGS: u32 := int_mod_of 32 1112%Z.

Definition INVALID_OPCODE_ERGS: u32 := ZMod.int_mod_of 32 (ZMod.unsigned_max 32).

Definition RICH_ADDRESSING_OPCODE_ERGS: u32
  := int_mod_of 32 (VM_CYCLE_COST_IN_ERGS.(int_val _) + 2 * RAM_PERMUTATION_COST_IN_ERGS.(int_val _)).
Definition AVERAGE_OPCODE_ERGS: u32
  := int_mod_of 32 (VM_CYCLE_COST_IN_ERGS.(int_val _)
                    + RAM_PERMUTATION_COST_IN_ERGS.(int_val _)).



Definition STORAGE_READ_IO_PRICE: u32 := int_mod_of 32 150%Z.
Definition STORAGE_WRITE_IO_PRICE: u32 :=int_mod_of 32  250%Z.
Definition EVENT_IO_PRICE: u32 :=int_mod_of 32  25%Z.
Definition L1_MESSAGE_IO_PRICE: u32 :=int_mod_of 32  100%Z.
Definition CALL_LIKE_ERGS_COST: u32 :=int_mod_of 32  20%Z.
Definition ERGS_PER_CODE_WORD_DECOMMITTMENT: u32 := CODE_DECOMMITMENT_COST_PER_WORD_IN_ERGS.

End Ergs.
