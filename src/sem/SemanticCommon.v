From RecordUpdate Require Import RecordSet.
Require Addressing Common Condition ExecutionStack Memory Instruction State MemoryOps ABI.

Import
Addressing
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

Import Addressing.Coercions.

Definition smallstep := state -> state -> Prop .

Definition reg_reserved := pv0.

Inductive update_pc_regular : execution_stack -> execution_stack -> Prop :=
| fp_update:
  forall pc' ef,
    let pc := pc_get ef in
    uinc_overflow _ pc = (pc',false) ->
    let ef' := pc_set pc' ef in
    update_pc_regular ef ef'.


Inductive grow_heap_page: mem_address -> active_pages -> active_pages -> Prop :=
| gp_heap: forall ap new_bound diff,
    ap.(ctx_heap_bound) + diff = (new_bound, false) ->
    grow_heap_page diff ap (ap <| ctx_heap_bound := new_bound |>).

Inductive grow_auxheap_page : mem_address -> active_pages -> active_pages -> Prop :=
| gp_auxheap: forall ap new_bound diff,
    ap.(ctx_auxheap_bound) + diff = (new_bound, false) ->
    grow_auxheap_page diff ap (ap <| ctx_auxheap_bound := new_bound |>).

Inductive grow_heap_variant: data_page_type -> mem_address -> active_pages -> active_pages -> Prop :=
| ghv_heap: forall diff ap ap',
    grow_heap_page diff ap ap' ->
    grow_heap_variant Heap diff ap ap'
| ghv_auxheap: forall diff ap ap',
    grow_auxheap_page diff ap ap' ->
    grow_heap_variant AuxHeap diff ap ap'.

Inductive grow_and_pay : data_page_type -> mem_address ->  execution_stack -> execution_stack -> Prop :=
  | pg_grow: forall heap_type query xstack0 xstack1 new_xstack new_apages diff,
      let current_bound := heap_variant_bound heap_type xstack0 in
      (diff, false) = query - current_bound ->
      pay (Ergs.growth_cost diff) xstack0 xstack1 ->
      let apages := get_active_pages xstack1 in
      grow_heap_variant heap_type diff apages new_apages ->
      new_xstack = update_memory_context new_apages xstack1 ->
      grow_and_pay heap_type query xstack0 new_xstack
  | pg_nogrow: forall heap_type query xstack0 diff,
      let current_bound := heap_variant_bound heap_type xstack0 in
      (diff, false) = query - current_bound ->
      grow_and_pay heap_type query xstack0 xstack0.
        
    
Inductive paid_forward: forward_page_type -> fat_ptr * execution_stack -> fat_ptr * execution_stack -> Prop :=
|pf_useheapvariant: forall type in_ptr xstack0 xstack1 query,
    validate_fresh in_ptr = no_exceptions ->
    in_ptr.(fp_start) + in_ptr.(fp_length) = (query, false) ->
    grow_and_pay type query xstack0 xstack1 ->
    paid_forward (UseMemory type) (in_ptr, xstack0) (in_ptr <| fp_page := active_heap_id xstack0 |>, xstack1)
|pf_forwardfatpointer: forall in_ptr xstack out_ptr,
    validate_non_fresh in_ptr = no_exceptions ->
    fat_ptr_shrink in_ptr out_ptr ->
    paid_forward ForwardFatPointer (in_ptr, xstack) (out_ptr, xstack)
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
