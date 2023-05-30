From RecordUpdate Require Import RecordSet.
Require Common Condition ExecutionStack Memory Instruction State MemoryOps ABI.

Import
ABI
ABI.FarCall
ABI.FatPointer
ABI.NearCall
ABI.Ret
Bool
CodeStorage
Common
Condition
ExecutionStack
Instruction
Instruction
Memory
MemoryBase
MemoryOps
RecordSetNotations
State
ZArith
ZBits
ZMod.

Import Arg Arg.Coercions.

Definition smallstep := state -> state -> Prop .

Definition reg_reserved := pv0.

Inductive update_pc_regular : execution_stack -> execution_stack -> Prop :=
| fp_update:
  forall pc' ef,
    let pc := pc_get ef in
    uinc_overflow _ pc = (pc',false) ->
    let ef' := pc_set pc' ef in
    update_pc_regular ef ef'.


Inductive pay_growth_or_burn: mem_address -> execution_stack -> execution_stack -> Prop  :=
| phg_affordable: forall ef ef' diff,
    let cost := Ergs.growth_cost diff in
    affordable ef cost = true ->
    pay cost ef ef' ->
    pay_growth_or_burn diff ef ef'
| phg_too_expensive: forall ef diff,
    let cost := Ergs.growth_cost diff in
    affordable ef cost = false ->
    pay_growth_or_burn diff ef (ergs_reset ef).

Inductive pay_growth_or_burn_ptr : mem_address -> fat_ptr -> execution_stack -> execution_stack -> Prop  :=
| pgb_ptr:forall current_bound ptr diff ef ef',
    fat_ptr_induced_growth ptr current_bound diff ->
    pay_growth_or_burn diff ef ef' ->
    pay_growth_or_burn_ptr current_bound ptr ef ef'.

Inductive pay_heaps_growth_or_burn: forward_page_type -> fat_ptr -> execution_stack -> execution_stack -> Prop  :=
| mpgb_forward p xstack:
  pay_heaps_growth_or_burn ForwardFatPointer p xstack xstack

| mpgb_heap in_ptr xstack0 xstack1:
  pay_growth_or_burn_ptr (heap_bound xstack0) in_ptr xstack0 xstack1 ->
  pay_heaps_growth_or_burn UseHeap in_ptr xstack0 xstack1
| mpgb_auxheap in_ptr xstack0 xstack1:
  pay_growth_or_burn_ptr (auxheap_bound xstack0) in_ptr xstack0 xstack1 ->
  pay_heaps_growth_or_burn UseAuxHeap in_ptr xstack0 xstack1.


Inductive grow_heap_page: mem_address -> active_pages -> active_pages -> Prop :=
| gp_heap: forall ap new_bound diff,
    ap.(ctx_heap_bound) + diff = (new_bound, false) ->
    grow_heap_page diff ap (ap <| ctx_heap_bound := new_bound |>).

Inductive grow_auxheap_page : mem_address -> active_pages -> active_pages -> Prop :=
| gp_auxheap: forall ap new_bound diff,
    ap.(ctx_auxheap_bound) + diff = (new_bound, false) ->
    grow_auxheap_page diff ap (ap <| ctx_auxheap_bound := new_bound |>).


Inductive select_page_bound : execution_stack -> Ret.forward_page_type -> page_id * mem_address -> Prop :=
| fpmspb_heap: forall ef,
    select_page_bound ef UseHeap
      (active_heap_id ef, (get_active_pages ef).(ctx_heap_bound))
| fpmspb_auxheap: forall ef,
    select_page_bound ef UseAuxHeap
      (active_auxheap_id ef, (get_active_pages ef).(ctx_auxheap_bound)).

Definition KERNEL_MODE_MAXADDR : contract_address := int_mod_of _ (2^16-1).

Definition addr_is_kernel (addr:contract_address) : bool :=
  lt_unsigned _ addr KERNEL_MODE_MAXADDR.

Definition in_kernel_mode (ef:callframe) : bool :=
  let ef := topmost_extframe ef in
  addr_is_kernel ef.(ecf_this_address).

Definition code_storage := code_storage _ instruction_invalid.
Definition code_manager := code_manager.


Definition revert_storage (ef:callframe_external) (d: depot) : depot :=
  let saved_storage := ef.(ecf_saved_storage_state) in
  let last_caller_address := resize _  contract_address_bits ef.(ecf_msg_sender) in
  store depot_params saved_storage last_caller_address d.
