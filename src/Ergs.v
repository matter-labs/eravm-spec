Require Common isa.Assembly TransientMemory.
Import Common Assembly TransientMemory ZArith.

Section Ergs.
Open Scope Z_scope.

(** # Ergs

**Ergs** is the resource spent on executing actions in EraVM.

The most common action consuming ergs is executing an instruction.
Instructions have a fixed [%base_cost], failure to pay this cost results in panic.

In EraVM, the instructions are [%predicated]. If an instruction is not executed
because of mismatch between their predicate [%ins_cond] with the current
[%gs_flags], its base cost is still paid.
Therefore, it is cheaper to jump over expensive instructions like [%OpFarCall]
than to predicate them so that they are not executed.

Additionally, actions like decommitting code for execution, accessing contract
storage, or growing memory bounds, also cost ergs.

Internally, ergs are 32-bit unsigned numbers.
*)

Definition ergs_bits := 32%nat.
Definition ergs := BITS ergs_bits.
Definition ergs_of : Z -> ergs := fromZ.

(** ## Ergs and callstack

Every frame in [%callstack], whether external or internal, keeps its associated ergs in the field [%cf_ergs_remaining].
Spending ergs decreases this value [%cf_ergs_remaining].


### Calls

Calling functions/contracts requires passing ergs to the new calling frame, so
that the callee's code would be able to operate and spend ergs (see e.g.
[%step_nearcall]).

For far calls, it is not possible to pass more than [%max_passable] ergs (currently 63/64 of ergs available in current frame).
For near calls, passing 0 ergs leads to passing all ergs in the current frame.

### Returns

If a function returns without panic, the remaining ergs are returned to its parent frame i.e. added to the parent frame's [%cf_ergs_remaining].

If a function panics, all its ergs are burned (see [%sem.Panic.step_panic]).
Panic does not burn ergs of parent frames.

The following return instructions lead to returning remaining ergs to the caller:

- [%OpNearRet]
- [%OpNearRetTo]
- [%OpRet]
- [%OpRevert]
- [%OpRevertTo]
- [%OpNearPanicTo]



## Actions consuming ergs

Each instruction has a fixed based cost that gets deducted before executing it (see [%base_cost]).

Additionally, the following actions lead to spending ergs:

1. Decommitting contract code. Performing far call to a contract which was not called during the construction of the current block costs ergs per each word of contract code. See [%Decommitter], [%FarCall].
2. TODO Accessing storage
3. Memory growth. Data pages holding heap variants are bounded, and only accesses to addresses within these bounds are free. Reading or writing to these pages outside bounds forces the **memory growth** with bound adjustment. The number of bytes by which the bounded area has grown has to be paid; see [%grow_and_pay].
4. Passing messages to L1 by [%OpToL1Message].

## Burning ergs

Burning ergs refers to a situation of panic, when the topmost [%callstack] frame
is destroyed with its allocated ergs.
The general rule is: if some invariant of execution breaks, VM panics, burning all ergs in the current frame.
This is a fail-fast behavior in case of irrecoverable errors.
Some examples are:

- using an integer value where pointer value is expected
- executing kernel-only instruction in user mode
- call stack overflow

Some situations that provoke panic are:

- having not enough ergs to pay, e.g. for memory growth;
- attempting to execute an instruction with an invalid encoding;
- attempting to execute kernel-only instruction in user mode.

See section [%Panics] for the full description.

## Parameters

The following definitions are used to derive the costs of instructions and other actions.
 *)

(* begin hide *)
#[reversible]
Local Coercion ergs_of : Z >-> ergs.
(* end hide *)


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

Definition MAX_TX_ERGS_LIMIT: Z := 80000000.

Definition VM_INITIAL_FRAME_ERGS: Z := unsigned_max 32.

Definition EVM_SIMULATOR_STIPEND: Z := 2^30.


Definition ERGS_PER_CIRCUIT: Z := 80000.


Definition INVALID_OPCODE_ERGS: Z := unsigned_max 32.

Definition RICH_ADDRESSING_OPCODE_ERGS: Z :=
    VM_CYCLE_COST_IN_ERGS + 2 * RAM_PERMUTATION_COST_IN_ERGS.
Definition AVERAGE_OPCODE_ERGS: Z := VM_CYCLE_COST_IN_ERGS + RAM_PERMUTATION_COST_IN_ERGS.



Definition STORAGE_READ_IO_PRICE: Z := 150.
Definition STORAGE_WRITE_IO_PRICE: Z := 250.
Definition EVENT_IO_PRICE: Z := 25.
Definition L1_MESSAGE_IO_PRICE: Z := 100.


Definition CALL_LIKE_ERGS_COST: Z := 20.

Definition ERGS_PER_CODE_WORD_DECOMMITTMENT: Z := CODE_DECOMMITMENT_COST_PER_WORD_IN_ERGS.


Definition VM_MAX_STACK_DEPTH: Z := VM_INITIAL_FRAME_ERGS / CALL_LIKE_ERGS_COST + 80.

Definition INITIAL_FRAME_SUCCESSFUL_EXIT_PC: Z := 0.
Definition INITIAL_FRAME_FORMAL_EH_LOCATION: Z := unsigned_max 16.

Definition SYSTEM_CONTRACTS_OFFSET_ADDRESS: Z := 2 ^ 15.

Definition KECCAK256_ROUND_FUNCTION_PRECOMPILE_ADDRESS: Z := SYSTEM_CONTRACTS_OFFSET_ADDRESS + 0x10.
Definition SHA256_ROUND_FUNCTION_PRECOMPILE_ADDRESS: Z := 0x02.
Definition ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS: Z := 0x01.
Definition SECP256R1_VERIFY_PRECOMPILE_ADDRESS: Z := 0x100.

Definition MAX_PUBDATA_COST_PER_QUERY: Z := 65.
Definition INITIAL_STORAGE_WRITE_PUBDATA_BYTES: Z := 64.
Definition REPEATED_STORAGE_WRITE_PUBDATA_BYTES: Z := 40.
Definition L1_MESSAGE_PUBDATA_BYTES: Z := 1 + 1 + 2 + 20 + 32 + 32.



Definition MAX_PUBDATA_PER_BLOCK: Z := 110000.

Definition STORAGE_AUX_BYTE: u8 := fromZ 0.
Definition EVENT_AUX_BYTE: u8 := fromZ 1.
Definition L1_MESSAGE_AUX_BYTE: u8 := fromZ 2.
Definition PRECOMPILE_AUX_BYTE: u8 := fromZ 3.
Definition TRANSIENT_STORAGE_AUX_BYTE: u8 := fromZ 4.


Definition BOOTLOADER_FORMAL_ADDRESS_LOW: Z := SYSTEM_CONTRACTS_OFFSET_ADDRESS + 0x01.
Definition DEPLOYER_SYSTEM_CONTRACT_ADDRESS_LOW: Z := SYSTEM_CONTRACTS_OFFSET_ADDRESS + 0x02.


Definition ADDRESS_UNRESTRICTED_SPACE: u64 := fromZ (2^16).

Definition ADDRESS_ECRECOVER: u16 := fromZ 0x0001.
Definition ADDRESS_SHA256: u16 := fromZ 0x0002.
Definition ADDRESS_RIPEMD160: u16 := fromZ 0x0003.
Definition ADDRESS_IDENTITY: u16 := fromZ 0x0004.

Definition ADDRESS_BOOTLOADER: u16 := fromZ 0x8001.
Definition ADDRESS_ACCOUNT_CODE_STORAGE: u16 := fromZ 0x8002.
Definition ADDRESS_NONCE_HOLDER: u16 := fromZ 0x8003.
Definition ADDRESS_KNOWN_CODES_STORAGE: u16 := fromZ 0x8004.
Definition ADDRESS_IMMUTABLE_SIMULATOR: u16 := fromZ 0x8005.
Definition ADDRESS_CONTRACT_DEPLOYER: u16 := fromZ 0x8006.
Definition ADDRESS_FORCE_DEPLOYER: u16 := fromZ 0x8007.
Definition ADDRESS_L1_MESSENGER: u16 := fromZ 0x8008.
Definition ADDRESS_MSG_VALUE: u16 := fromZ 0x8009.
Definition ADDRESS_ETH_TOKEN: u16 := fromZ 0x800A.
Definition ADDRESS_SYSTEM_CONTEXT: u16 := fromZ 0x800B.
Definition ADDRESS_BOOTLOADER_UTILITIES: u16 := fromZ 0x800C.
Definition ADDRESS_EVENT_WRITER: u16 := fromZ 0x800D.
Definition ADDRESS_KECCAK256: u16 := fromZ 0x8010.

Definition BOOTLOADER_MAX_MEMORY: Z := unsigned_max 32.

Definition NEW_FRAME_MEMORY_STIPEND: Z := 2^12.


Definition NEW_KERNEL_FRAME_MEMORY_STIPEND: Z := 2^21.

Definition INTERNAL_ERGS_TO_VISIBLE_ERGS_CONVERSION_CONSTANT: Z := 1.



Definition MAX_AUTOMATICALLY_SUPPORTED_MSG_VALUE_BYTECODE: Z := 100000.
Definition DECOMMITMENT_MSG_VALUE_SIMULATOR_OVERHEAD: Z :=
    ERGS_PER_CODE_WORD_DECOMMITTMENT * MAX_AUTOMATICALLY_SUPPORTED_MSG_VALUE_BYTECODE / 32.


Definition MSG_VALUE_SIMULATOR_ADDITIVE_COST: Z :=
    14500 + DECOMMITMENT_MSG_VALUE_SIMULATOR_OVERHEAD.


Definition MIN_STORAGE_WRITE_PRICE_FOR_REENTRANCY_PROTECTION: Z := 2300 + 1.


Definition MIN_STORAGE_WRITE_COST: Z := Z.max MIN_STORAGE_WRITE_PRICE_FOR_REENTRANCY_PROTECTION STORAGE_WRITE_HASHER_MIN_COST_IN_ERGS.

Definition STORAGE_ACCESS_COLD_READ_COST: Z := 2000.
Definition STORAGE_ACCESS_COLD_WRITE_COST: Z := Z.max MIN_STORAGE_WRITE_COST 5500.


Definition MSG_VALUE_SIMULATOR_MIN_USED_ERGS: Z := 8000 + DECOMMITMENT_MSG_VALUE_SIMULATOR_OVERHEAD.


Definition growth_cost (diff:mem_address) : ergs := diff.
End Ergs.

Section Costs.
  Open Scope Z_scope.
(** # Costs

Basic costs of all instructions. They are paid when the instruction starts
executing; see [%Semantics.step].

Instructions may also impose additional costs e.g. far returns and far calls may
grow heap; far calls also may induce code
[%decommitment_cost].
 *)
  Definition base_cost (ins:asm_instruction) :=
    (match ins with
     | OpInvalid => INVALID_OPCODE_ERGS
     | OpNoOp | OpSpAdd _ _ | OpSpSub _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpJump _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpAnd _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpOr _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpXor _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpAdd _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpSub _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS

     | OpShl _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpShr _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpRol _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpRor _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS

     | OpMul _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpDiv _ _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpNearCall _ _ _ => AVERAGE_OPCODE_ERGS + CALL_LIKE_ERGS_COST
     | OpFarCall _ _ _ _ _
     | OpDelegateCall _ _ _ _ _
     | OpMimicCall _ _ _ _ _ => 2 * VM_CYCLE_COST_IN_ERGS
                               + RAM_PERMUTATION_COST_IN_ERGS
                               + STORAGE_READ_IO_PRICE
                               + CALL_LIKE_ERGS_COST
                               + STORAGE_SORTER_COST_IN_ERGS
                               + CODE_DECOMMITMENT_SORTER_COST_IN_ERGS

     | OpNearRetTo _ | OpNearRevertTo _ | OpNearPanicTo _
     | OpRet _ | OpRevert _
     | OpPanic
       => AVERAGE_OPCODE_ERGS
     | OpPtrAdd _ _ _ _
     | OpPtrSub _ _ _ _
     | OpPtrShrink _ _ _ _
     | OpPtrPack _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     |
       OpStore _ _ _
     | OpStoreInc _ _ _ _
     | OpStaticWrite _ _
     | OpStaticWriteInc _ _ _
       => 2 * VM_CYCLE_COST_IN_ERGS + 5 * RAM_PERMUTATION_COST_IN_ERGS

     | OpLoad _ _ _
     | OpLoadInc _ _ _ _
     | OpLoadPointer _ _
     | OpLoadPointerInc _ _ _
     | OpStaticRead _ _
     | OpStaticReadInc _ _ _
       => VM_CYCLE_COST_IN_ERGS + 3 * RAM_PERMUTATION_COST_IN_ERGS

     | OpContractThis _
     | OpContractCaller _
     | OpContractCodeAddress _
     | OpVMMeta _
     | OpVMErgsLeft _
     | OpVMSP _
     | OpGetCapturedContext _
     | OpSetContextReg _
     | OpAuxMutating _
     | OpIncrementTxNumber
       => AVERAGE_OPCODE_ERGS

     | OpSLoad _ _=> VM_CYCLE_COST_IN_ERGS
                    + RAM_PERMUTATION_COST_IN_ERGS
                    + LOG_DEMUXER_COST_IN_ERGS
                    + STORAGE_SORTER_COST_IN_ERGS
                    + STORAGE_ACCESS_COLD_READ_COST
     | OpSStore _ _ => VM_CYCLE_COST_IN_ERGS
                    + RAM_PERMUTATION_COST_IN_ERGS
                    + 2 * LOG_DEMUXER_COST_IN_ERGS
                    + 2 * STORAGE_SORTER_COST_IN_ERGS
                    + STORAGE_ACCESS_COLD_WRITE_COST

     | OpToL1Message _ _ _ => L1_MESSAGE_IO_PRICE
                    + VM_CYCLE_COST_IN_ERGS
                    + RAM_PERMUTATION_COST_IN_ERGS
                    + 2 * LOG_DEMUXER_COST_IN_ERGS
                    + 2 * EVENTS_OR_L1_MESSAGES_SORTER_COST_IN_ERGS
     | OpEvent _ _ _ => EVENT_IO_PRICE
                    + VM_CYCLE_COST_IN_ERGS
                    + RAM_PERMUTATION_COST_IN_ERGS
                    + 2 * LOG_DEMUXER_COST_IN_ERGS
                    + 2 * EVENTS_OR_L1_MESSAGES_SORTER_COST_IN_ERGS

     | OpPrecompileCall _ _ _
     | OpDecommit _ _ _ =>
         VM_CYCLE_COST_IN_ERGS + RAM_PERMUTATION_COST_IN_ERGS + LOG_DEMUXER_COST_IN_ERGS
     | OpTransientLoad _ _ =>
         VM_CYCLE_COST_IN_ERGS
         + RAM_PERMUTATION_COST_IN_ERGS
         + LOG_DEMUXER_COST_IN_ERGS
         + STORAGE_SORTER_COST_IN_ERGS
     | OpTransientStore _ _ =>
         VM_CYCLE_COST_IN_ERGS
         + RAM_PERMUTATION_COST_IN_ERGS
         + 2 * LOG_DEMUXER_COST_IN_ERGS
         + 2 * STORAGE_SORTER_COST_IN_ERGS
     end)%Z.


(** Implementation note: Coq allows partially evaluating [%base_cost] to get the absolute erg costs for each instruction:

```
Compute base_costs.
```

Current costs are:
```
| Invalid => 4294967295
| NearCall => 25
| FarCall
| MimicCall
| DelegateCall => 182
| NearRet
| NearRetTo
| FarRet
| NearRevert
| NearRevertTo
| FarRevert
| NearPanicTo
| Panic
| ContractThis
| ContractCaller
| ContractCodeAddress
| VMMeta
| VMErgsLeft
| VMSp
| GetCapturedContext
| SetContextReg
| IncrementTxNumber
| AuxMutating => 5
| SLoad => 2008
| SStore => 5511
| Event => 34
| ToL1Message => 109
| TransientWrite => 11
| TransientRead => 8
| Load
| LoadInc
| LoadPointer
| LoadPointerInc
| StaticRead
| StaticReadInc => 7
| Store
| StoreInc
| StaticWrite
| StaticWriteInc => 13
| <otherwise> => 6
```
 *)
  Compute base_cost.

End Costs.
