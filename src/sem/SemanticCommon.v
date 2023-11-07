From RecordUpdate Require Import RecordSet.

Require
ABI
Addressing
Binding
CallStack
Common
Flags
KernelMode
MemoryContext
MemoryOps
State
Steps
TransientMemory
VMPanic
sem.StepPanic
.

Import ssreflect ssrfun ssrbool eqtype ssreflect.tuple.

Import
  Addressing
    Bool
    Common
    Coder
    Core
    Flags
    CallStack
    Decommitter
    Ergs
    GPR
    List
    ListNotations
    KernelMode
    MemoryContext
    memory.Depot
    MemoryBase
    MemoryOps
    Pointer
    PrimitiveValue
    RecordSetNotations
    State
    TransientMemory
    ZArith
    ZBits.
Export Steps Binding VMPanic StepPanic.

Section Params.
  Open Scope ZMod_scope.
  Definition MAX_OFFSET_TO_DEREF_LOW_U32: u32 := fromZ (2^32 - 33)%Z.
  Definition MAX_OFFSET_FOR_ADD_SUB: u256 := fromZ (2^32)%Z.
End Params.


Section Depot.
  Definition is_rollup (xstack: callstack) : bool := zero8 == current_shard xstack.
  Definition net_pubdata cs : Z := if is_rollup cs then INITIAL_STORAGE_WRITE_PUBDATA_BYTES else 0%Z.

End Depot.

Definition current_storage_fqa (xstack:callstack) : fqa_storage :=
  mk_fqa_storage (current_shard xstack) (current_contract xstack).


(* FIXME *)
Local Open Scope ZMod_scope.
Definition bitwise_flags (result: Core.word) : Flags.flags_state := Flags.bflags false (result == zero256) false.

Definition topmost_128_bits_match (x y : Core.word) : Prop := @high 128 128 x = @high 128 128 y.
