From RecordUpdate Require Import RecordSet.
Require Addressing Binding Common Flags CallStack Memory MemoryContext State MemoryOps ABI KernelMode Steps VMPanic sem.StepPanic.

Import
  Addressing
    Bool
    Common
    Coder
    Flags
    CallStack
    Decommitter
    Ergs
    GPR
    List
    ListNotations
    KernelMode
    Memory
    MemoryContext
    MemoryBase
    MemoryOps
    Pointer
    PrimitiveValue
    RecordSetNotations
    State
    ZArith
    ZBits
    ZMod.
Export Steps Binding VMPanic StepPanic.

Section Params.
  Open Scope ZMod_scope.
  Definition MAX_OFFSET_TO_DEREF_LOW_U32: u32 := int_mod_of _ (2^32 - 33)%Z.
End Params.


Section Payment.
  Open Scope ZMod_scope.


End Payment.

Definition in_kernel_mode (ef:callstack) : bool :=
  let ef := active_extframe ef in
  addr_is_kernel ef.(ecf_this_address).


Section Depot.

  Open Scope ZMod_scope.
  Definition is_rollup (xstack: callstack) : bool := zero8 == current_shard xstack.

  Definition net_pubdata xstack : Z := if is_rollup xstack then INITIAL_STORAGE_WRITE_PUBDATA_BYTES else 0.

End Depot.

Definition current_storage_fqa (xstack:callstack) : fqa_storage :=
  mk_fqa_storage (current_shard xstack) (current_contract xstack).


(* FIXME *)
Import ZMod.
Local Open Scope ZMod_scope.
Definition bitwise_flags (result: Core.word) : Flags.flags_state := Flags.bflags false (result == zero256) false.

Definition topmost_128_bits_match (x y : Core.word) : Prop := ZMod.shiftr _ (int_mod_of _ 128) x = ZMod.shiftr _ (int_mod_of _ 128) y.
