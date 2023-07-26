Require lib.ZMod Common Instruction Memory.
Import Common Instruction Memory ZMod ZArith.

Section Ergs.
Open Scope Z_scope.

(** # Ergs

**Ergs** is the resource spent on executing actions in EraVM.

The most common action consuming ergs is executing an instruction.
Executing an instruction has a fixed [%base_cost]; if the current balance is lower than the cost, VM panics.
If an instruction is not executed because of mismatch between their execution condition [%cond] with the current [%flags_state] in [%state], its base cost is still paid.
Therefore it is cheaper to jump over expensive instructions like [%OpFarCall] than to predicate them.

Additionally, actions like decommitting code for execution, accessing contract storage, or growing memory bounds, also cost ergs.

Internally, ergs are 32-bit unsigned numbers.
 *)

Definition ergs_bits := 32%nat.
Definition ergs := int_mod ergs_bits.
Definition ergs_of := int_mod_of ergs_bits.

(** ## Ergs balance in callstack

Every frame in [%callstack], whether external or internal, keeps its proper independent ergs balance in the field [%cf_ergs_remaining].

Calling functions/contracts requires passing ergs to the new calling frame, so that the callee's code would be able to function by spending ergs (see e.g. [%step_nearcall]).

For far calls, it is not possible to pass more than [%FarCall.max_passable] ergs (currently 63/64 of the balance in current frame).
For near calls, passing 0 ergs leads to passing all ergs in the current frame.

If a function panics, all its ergs are burned (see [%sem.Panic.step_panic]).
Panic does not burn ergs of parent frames.

If the function returns without panic, the remaining ergs are returned to its parent frame i.e. added to the parent frame's [%cf_ergs_remaining].

The following return instructions lead to returning remaining ergs to the caller:

- [%OpNearRet]
- [%OpNearRetTo]
- [%OpFarRet]
- [%OpNearRevert]
- [%OpNearRevertTo]
- [%OpFarRevert]
- [%OpNearPanicTo]



## Actions consuming ergs

Each instruction has a fixed based cost that gets deducted before executing it (see [%base_cost]).

Additionally, the following actions lead to spending ergs:

1. Decommitting contract code. Performing far call to a contract which was not called during the construction of the current block costs ergs per each word of contract code. See [%Decommitter], [%FarCall].
2. TODO Accessing storage
3. Memory growth. Data pages holding heap variants are bound, and only accesses to addresses within these bounds are free. Reading or writing to these pages leads to bound being increased; the difference between [%grow_and_pay] growth.
4. Passing messages to L1 by [%OpToL1Message].


## Burning ergs

Burning ergs refers to setting erg balance to zero for the current frame, and executing [%OpPanic].

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


## Parameters

The following definitions are used to derive the costs of instructions and other actions.
 *)

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

Section Costs.
  Import ZMod ZArith.

  Open Scope Z_scope.
(** # Costs

Basic costs of all instructions. They get deducted when the instruction starts
executing; see [%Semantics.step].

Instructions may also impose additional costs e.g. far returns and far calls may grow heap; farcalls also may induce code decommittment costs.
 *)
  Definition base_cost {descr} (ins:@instruction descr) :=
    (match ins with
     | OpInvalid => INVALID_OPCODE_ERGS
     | OpNoOp | OpModSP _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpJump _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpAnd _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpOr _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpXor _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpAdd _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpSub _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS

     | OpShl _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpShr _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpRol _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpRor _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS

     | OpMul _ _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
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

     | OpNearRet | OpNearRetTo _ | OpNearRevert | OpNearRevertTo _ | OpNearPanicTo _
     | OpFarRet _ | OpFarRevert _
     | OpPanic
       => AVERAGE_OPCODE_ERGS
     | OpPtrAdd _ _ _ _
     | OpPtrSub _ _ _ _
     | OpPtrShrink _ _ _ _
     | OpPtrPack _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     |
       OpStore _ _ _
     | OpStoreInc _ _ _ _
       => 2 * VM_CYCLE_COST_IN_ERGS + 5 * RAM_PERMUTATION_COST_IN_ERGS

     | OpLoad _ _ _
     | OpLoadInc _ _ _ _
     | OpLoadPointer _ _
     | OpLoadPointerInc _ _ _
       => VM_CYCLE_COST_IN_ERGS + 3 * RAM_PERMUTATION_COST_IN_ERGS

     | OpContextThis _
     | OpContextCaller _
     | OpContextCodeAddress _
     | OpContextMeta _
     | OpContextErgsLeft _
     | OpContextSp _
     | OpContextGetContextU128 _
     | OpContextSetContextU128 _
     | OpContextSetErgsPerPubdataByte _
     | OpContextIncrementTxNumber => AVERAGE_OPCODE_ERGS
     | OpSLoad _ _=> STORAGE_READ_IO_PRICE
                 + VM_CYCLE_COST_IN_ERGS
                 + RAM_PERMUTATION_COST_IN_ERGS
                 + LOG_DEMUXER_COST_IN_ERGS
                 + STORAGE_SORTER_COST_IN_ERGS
     | OpSStore _ _ =>
                Z.max MIN_STORAGE_WRITE_COST (
                    STORAGE_WRITE_IO_PRICE
                    + 2 * VM_CYCLE_COST_IN_ERGS
                    + RAM_PERMUTATION_COST_IN_ERGS
                    + 2 * LOG_DEMUXER_COST_IN_ERGS
                    + 2 * STORAGE_SORTER_COST_IN_ERGS)
     | OpToL1Message _ _ _ =>
                let intrinsic_cost := L1_MESSAGE_IO_PRICE
                    + 2 * VM_CYCLE_COST_IN_ERGS
                    + RAM_PERMUTATION_COST_IN_ERGS
                    + 2 * LOG_DEMUXER_COST_IN_ERGS
                    + 2 * EVENTS_OR_L1_MESSAGES_SORTER_COST_IN_ERGS in
                Z.max intrinsic_cost L1_MESSAGE_MIN_COST_IN_ERGS
     | OpEvent _ _ _ => EVENT_IO_PRICE
                     + 2 * VM_CYCLE_COST_IN_ERGS
                     + RAM_PERMUTATION_COST_IN_ERGS
                     + 2 * LOG_DEMUXER_COST_IN_ERGS
                     + 2 * EVENTS_OR_L1_MESSAGES_SORTER_COST_IN_ERGS
     | OpPrecompileCall _ _ =>
         VM_CYCLE_COST_IN_ERGS + RAM_PERMUTATION_COST_IN_ERGS + LOG_DEMUXER_COST_IN_ERGS
     end)%Z.

(** Coq allows partially evaluating [%base_cost] to get the absolute erg costs for each instruction:

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
| Store
| StoreInc => 13
| Load
| LoadInc
| LoadPointer
| LoadPointerInc => 7
| NearRet
| NearRetTo
| FarRet
| NearRevert
| NearRevertTo
| FarRevert
| NearPanicTo
| Panic
| ContextThis
| ContextCaller
| ContextCodeAddress
| ContextMeta
| ContextErgsLeft
| ContextSp
| ContextGetContextU128
| ContextSetContextU128
| ContextSetErgsPerPubdataByte
| ContextIncrementTxNumber => 5
| SLoad => 158
| SStore => 3501
| ToL1Message => 156250
| Event => 38
| <otherwise> => 6
```
 *)
  Compute base_cost.

End Costs.
