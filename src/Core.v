Require Common lib.ZMod.

Import ZMod Common ZArith.
(**
A **word** is a 256-bit unsigned number.

A **cell** is a memory unit for stack, registers, storage  an alias for word.
 *)

Definition word_bits: nat := 256.



Definition word: Set := ZMod.int_mod word_bits.
Definition word0: word := ZMod.int_mod_of word_bits 0%Z.

Section Helpers.
  Import Nat.
  Definition bytes_in_word : nat := word_bits/bits_in_byte.
  Definition z_bytes_in_word : Z := Z.of_nat bytes_in_word.
End Helpers.


Definition timestamp := nat.
Definition tx_num := u16.
