Require Common isa.CoreSet.
Import Common isa.CoreSet.

Section Panics.
  (** # Panic

**Panic** refers to a situation of irrecoverable error.
It can occur for one of the following reasons:

- There are not enough ergs to execute an action.
- Executing an instruction requiring kernel mode in user mode.
- Executing an instruction mutating global state in static mode.
- Violation of one of VM inner invariants.
- Overflow of callstack.
- Attempt to execute an invalid instruction.
-
Providing an integer value (with the tag cleared) instead of a pointer value (with the tag set) to an instruction that expects a tagged fat pointer value, e.g. [%OpPtrAdd].

## Complete list of panic reasons

The type [%reason] describes all situations where EraVM panics.

**Note** this is an exhaustive list! If there is a panic situation which does not match to any condition described by [%reason], please, report it to Igor `iz@matterlabs.dev`.
   *)
  Inductive reason :=
  (** - See [%step_RetExt_ForwardFatPointer_requires_ptrtag]. *)
  | RetABIExistingFatPointerWithoutTag
  (** - See [%step_RetExt_ForwardFatPointer_returning_older_pointer]. *)
  | RetABIReturnsPointerCreatedByCaller
  (** - Malformed [%fat_ptr] is such that [%validate] returns [%false].*)
  | FatPointerMalformed
  (** - See [%step_PtrAdd_overflow] and [%step_PtrSub_underflow]. *)
  | FatPointerOverflow
  (** - See [%step_PtrAdd_diff_too_large] and [%step_PtrSub_diff_too_large]. *)
  | FatPointerDeltaTooLarge
  (** - See e.g. [%step_RetExt_heapvar_growth_unaffordable] *)
  | FatPointerCreationUnaffordable
  (** - See [%chose_action]. *)
  | NotInKernelMode
  (** - See [%chose_action]. *)
  | ForbiddenInStaticMode
  (** - See [%chose_action]. *)
  | CallStackOverflow
  (** - See [%step_PtrPack_notzero]. *)
  | PtrPackExpectsOp2Low128BitsZero
  (** - Instruction expects a tagged [%fat_ptr], e.g. [%step_PtrAdd_in1_not_ptr]. *)
  | ExpectedFatPointer
  (** - Instruction expects a non-tagged primitive value, e.g. [%step_PtrAdd_in2_ptr]. *)
  | ExpectedInteger
  (** - Executing [%OpPanic] or [%OpNearPanicTo]. *)
  | TriggeredExplicitly
  (** - Attempt to dereference a pointer past [%MAX_OFFSET_TO_DEREF_LOW_U32]. *)
  | HeapPtrOffsetTooLarge
  (** - Not enough ergs to pay for growing heap beyound the current bound. *)
  | HeapGrowthUnaffordable
  (** - Incrementing a heap pointer by executing [%OpLoadInc] or [%OpStoreInc] results in overflow. *)
  | HeapPtrIncOverflow
  (** - Incrementing a fat pointer by executing [%OpLoadPtrInc] results in overflow. *)
  | FatPtrIncOverflow
  (** - Instructions e.g. [%OpLoad] expect a heap pointer with a [%is_ptr] tag reset, not a fat pointer with a set tag. *)
  | ExpectedHeapPointer
  (** - Not enough ergs to pay [%base_cost] of instruction. Reminder: the cost is paid even if instruction is skipped by predication. *)
  | NotEnoughErgsToPayBaseCost
  (** - Far call expects to return an existing [%fat_ptr] but the provided value is not tagged as pointer. *)
  | FarCallInputIsNotPointerWhenExpected
  (** - Far call expects the storage of [%DEPLOYER_SYSTEM_CONTRACT_ADDRESS] to hold a valid [%versioned_hash] for the callee contract, but the hash for the callee contract is malformed. *)
  | FarCallInvalidCodeHashFormat
  (** - In a far call, not enough ergs to pay for code decommitment. *)
  | FarCallNotEnoughErgsToDecommit
  (** - In a far call, attempt to return a new [%fat_ptr] but it requires growing heap and there are not enough ergs to pay for this growth. *)
  | FarCallNotEnoughErgsToGrowMemory
  (** - Trying to far call a contract whose code is not yet deployed. *)
  | FarCallCallInNowConstructedSystemContract
  (** - Attempt to write to a storage by executing [%OpSStore] but not enough ergs to pay the associated cost. See [%step_SStore_unaffordable]. *)
  | StorageWriteUnaffordable
  .

  Inductive status :=
  | NoPanic
  | Panic : reason -> status
  .

End Panics.
