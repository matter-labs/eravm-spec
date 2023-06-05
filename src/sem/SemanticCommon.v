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

Inductive paid_forward: forward_page_type -> fat_ptr * execution_stack -> fat_ptr * execution_stack -> Prop :=
|pf_useheap: forall diff in_ptr xstack0 xstack1,
    let bound := heap_bound xstack0 in
    validate_fresh in_ptr = no_exceptions ->
    fat_ptr_induced_growth in_ptr bound diff ->
    pay_growth_or_burn diff xstack0 xstack1 ->
    paid_forward UseHeap (in_ptr, xstack0) (in_ptr <| fp_page := active_heap_id xstack0 |>, xstack1)

|pf_useauxheap: forall diff in_ptr xstack0 xstack1,
    let bound := auxheap_bound xstack0 in
    validate_fresh in_ptr = no_exceptions ->
    fat_ptr_induced_growth in_ptr bound diff ->
    pay_growth_or_burn diff xstack0 xstack1 ->
    paid_forward UseAuxHeap (in_ptr, xstack0) (in_ptr <| fp_page := active_heap_id xstack0 |>, xstack1)

|pf_forwardfatpointer: forall in_ptr xstack out_ptr,
    validate_non_fresh in_ptr = no_exceptions ->
    fat_ptr_shrink in_ptr out_ptr ->
    paid_forward ForwardFatPointer (in_ptr, xstack) (out_ptr, xstack)
.

Inductive paid_forward_and_adjust_bounds: forward_page_type -> fat_ptr * execution_stack * active_pages  -> fat_ptr * execution_stack * active_pages -> Prop :=
|fcf_useheap: forall diff in_ptr xstack0 xstack1 out_ptr old_apages grown_apages,
    paid_forward UseHeap (in_ptr, xstack0) (out_ptr, xstack1) ->
    let bound := heap_bound xstack0 in
    grow_heap_page diff old_apages grown_apages ->
    paid_forward_and_adjust_bounds UseHeap (in_ptr, xstack0, old_apages) (out_ptr, xstack1, grown_apages)

|fcf_useauxheap: forall diff in_ptr xstack0 xstack1 out_ptr old_apages grown_apages,
    paid_forward UseAuxHeap (in_ptr, xstack0) (out_ptr, xstack1) ->
    let bound := auxheap_bound xstack0 in
    grow_auxheap_page diff old_apages grown_apages ->
    paid_forward_and_adjust_bounds UseAuxHeap (in_ptr, xstack0, old_apages) (out_ptr, xstack1, grown_apages)

|fcf_forwardfatpointer: forall in_ptr xstack0 xstack1 pages out_ptr,
    paid_forward ForwardFatPointer (in_ptr, xstack0) (out_ptr, xstack1) ->
    paid_forward_and_adjust_bounds ForwardFatPointer (in_ptr, xstack0, pages) (out_ptr, xstack1,pages)
.
Definition KERNEL_MODE_MAXADDR : contract_address := int_mod_of _ (2^16-1).

Definition addr_is_kernel (addr:contract_address) : bool :=
  lt_unsigned _ addr KERNEL_MODE_MAXADDR.

Definition in_kernel_mode (ef:callframe) : bool :=
  let ef := topmost_extframe ef in
  addr_is_kernel ef.(ecf_this_address).

Definition code_storage := code_storage _ instruction_invalid.
Definition code_manager := code_manager.


Definition revert_storage (ef:callframe_external) : depot :=
  ef.(ecf_saved_depot).



Inductive fetch_apply2:
  (regs_state * execution_stack * pages) ->
  in_any -> in_reg -> out_any ->
  primitive_value -> primitive_value -> primitive_value ->
  (regs_state * execution_stack * pages)
  -> Prop :=

 | fa_apply:  forall xstack0 regs (in1:in_any) loc1 (in2:in_reg) loc2 xstack1 pages (out:out_any) out_loc val1 val2 result new_regs new_pages new_xstack,
  resolve xstack0 regs in1 loc1 ->
  resolve_effect__in in1 xstack0 xstack1 ->
  resolve xstack1 regs in2 loc2 ->
  resolve xstack1 regs out out_loc ->
  resolve_effect__out out xstack1 new_xstack ->
  fetch_loc regs new_xstack pages loc1 (FetchPV val1) ->
  fetch_loc regs new_xstack pages loc2 (FetchPV val2) ->
  store_loc regs new_xstack pages result  out_loc (new_regs, new_pages) ->

  fetch_apply2 (regs,xstack0,pages)
              in1 in2 out
              val1 val2 result
              (new_regs, new_xstack, new_pages)
.

Inductive fetch_apply2_swap swap:
  (regs_state * execution_stack * pages) ->
  in_any -> in_reg -> out_any ->
  primitive_value -> primitive_value -> primitive_value ->
  (regs_state * execution_stack * pages)
  -> Prop :=
 | fas_apply:  forall xstack0 regs (in1:in_any) (in2:in_reg) pages (out:out_any) val1 val2 val1' val2' result new_regs new_pages new_xstack,
  fetch_apply2 (regs,xstack0,pages)
              in1 in2 out
              val1 val2 result
              (new_regs, new_xstack, new_pages) ->
  apply_swap swap val1 val2 = (val1', val2') ->
  fetch_apply2_swap swap (regs,xstack0,pages)
              in1 in2 out
              val1' val2' result
              (new_regs, new_xstack, new_pages) .
