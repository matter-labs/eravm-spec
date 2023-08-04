From RecordUpdate Require Import RecordSet.
Require Addressing Binding Common Flags CallStack Memory MemoryContext State MemoryOps ABI KernelMode Steps VMPanic.

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
Export Steps Binding.

Section Params.
  Open Scope ZMod_scope.
  Definition MAX_OFFSET_TO_DEREF_LOW_U32: u32 := int_mod_of _ (2^32 - 33)%Z.
End Params.


Section Payment.
  Open Scope ZMod_scope.

  Inductive grow_and_pay : data_page_type -> mem_address ->  callstack -> callstack -> Prop :=
  | pg_grow: forall heap_type query xstack0 xstack1 new_xstack new_apages diff,
      let current_bound := heap_variant_bound heap_type xstack0 in
      (diff, false) = query - current_bound ->
      pay (Ergs.growth_cost diff) xstack0 xstack1 ->
      let apages := get_mem_ctx xstack1 in
      grow_heap_variant heap_type diff apages new_apages ->
      new_xstack = update_memory_context new_apages xstack1 ->
      grow_and_pay heap_type query xstack0 new_xstack
  | pg_nogrow: forall heap_type query xstack0 diff,
      let current_bound := heap_variant_bound heap_type xstack0 in
      (diff, false) = query - current_bound ->
      grow_and_pay heap_type query xstack0 xstack0.



  Inductive paid_forward_heap_span: data_page_type -> span * callstack -> fat_ptr * callstack -> Prop :=
  |pf_useheapvariant: forall start length heap_id type xstack0 xstack1 query,
      let span := mk_span start length in
      start + length = (query, false) ->
      grow_and_pay type query xstack0 xstack1 ->
      heap_id = Some (active_heap_id xstack0) ->
      paid_forward_heap_span type (span, xstack0) (mk_fat_ptr heap_id (fresh_ptr span), xstack1).

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
