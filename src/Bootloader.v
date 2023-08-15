Require Memory.

Import Memory ZMod.

Section Bootloader.
  Import ZArith.
  Open Scope Z.
(** # Bootloader

 Bootloader is a system contract in charge of block construction
([sources](https://github.com/matter-labs/system-contracts/blob/main/bootloader/bootloader.yul)).


Formally, bootloader is assigned an address
[%BOOTLOADER_SYSTEM_CONTRACT_ADDRESS], but on execution start EraVM decommits its
code directly by its [%versioned_hash].
*)
  Definition BOOTLOADER_SYSTEM_CONTRACT_ADDRESS : contract_address := int_mod_of _ ((2^15) + 1).

(** Using the bootloader [%versioned_hash], EraVM queries the bootloader code from
decommitter and starts executing it.

The heap page of the bootloader is different from other pages: it acts as an
interface between server and EraVM.
Server is able to modify the contents of this page at will.
Server gradually fills it with transaction data, formatted according to an
implementation-defined convention.

The bootloader then acts roughly as the following code (not an actual implementation):

```solidity
contract Bootloader {
	function executeBlock(
		address operatorAddress,
	  Transaction[2] memory transactions
	) {
     for(uint i = 0; i < transactions.length; i++) {
        validateTransaction(transactions[i]);
        chargeFee(operatorAddress, transactions[i]);
        executeTransaction(transactions[i]);
     }
  }

	function validateTransaction(Transaction memory tx) {
    // validation logic
	}
  function chargeFee(address operatorAddress, Transaction memory tx) {
    // charge fee
	}
  function executeTransaction(Transaction memory tx) {
    // execution logic
  }
}
```

The bootloader is therefore responsible for:

- validating transactions;
- executing transactions to form a new block;
- setting some of the transaction- or block-wide transaction parameters (e.g. blockhash, tx.origin).

Server makes a snapshot of EraVM state after completing every transaction. When
the bootloader encounters a malformed transaction, it fails, and the server
restarts EraVM from the most recent snapshot, skipping this transaction.
If a transaction is well-formed, EraVM may still panic while handling it outside
the bootloader code.
This is a normal situation and is handled by EraVM in a regular way, through panics. See e.g. [%OpPanic].

The exact code of the bootloader is a part of a protocol; its [%versioned_hash]
is included in the block header.
 *)

End Bootloader.
