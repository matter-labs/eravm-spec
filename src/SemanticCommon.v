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

Inductive binop_effect: execution_stack -> regs_state -> pages -> flags_state ->
                        in_any -> in_any -> out_any ->
                        mod_swap -> mod_set_flags ->
                        (word_type -> word_type -> (word_type * flags_state)) ->
                        (execution_stack * regs_state * pages * flags_state) -> Prop :=
| be_apply:
  forall f ef0 ef1 ef' regs regs' mm mm' (in1 in2: in_any) (out: out_any) loc1 loc2
    op1 op2 op1' op2' swap set_flags out_loc result flags_candidate flags0 new_flags,
    resolve ef0 regs in1 loc1 ->
    resolve_effect__in in1 ef0 ef1 ->
    resolve ef1 regs in2 loc2 ->
    resolve ef1 regs out out_loc ->
    resolve_effect__out out ef1 ef' ->
    fetch_loc regs ef' mm loc1 (FetchPV (IntValue op1)) ->
    fetch_loc regs ef' mm loc2 (FetchPV (IntValue op2)) ->
    apply_swap swap op1 op2 = (op1', op2') ->
    f op1' op2' = (result, flags_candidate) ->
    store_loc regs ef' mm (IntValue result) out_loc (regs', mm') ->
    new_flags = apply_set_flags set_flags flags0 flags_candidate ->
    binop_effect ef0 regs mm flags0 in1 in2 out swap set_flags f (ef', regs', mm', new_flags).

Inductive binop_step: in_any -> in_any -> out_any -> mod_swap -> mod_set_flags ->
                      (word_type -> word_type -> (word_type * flags_state)) ->
                      smallstep :=
| be_apply_step:
  forall f xstack new_xstack context_u128 regs new_regs pages new_pages depot (in1 in2: in_any) (out: out_any) swap set_flags flags new_flags codes,
    let gs := {|
          gs_flags        := flags;
          gs_callstack    := xstack;
          gs_regs         := regs;
          gs_context_u128 := context_u128;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_contracts    := codes;
          |}  in
    binop_effect xstack regs pages flags in1 in2 out swap set_flags f (new_xstack, new_regs, new_pages, new_flags) ->
    binop_step
      in1 in2 out swap set_flags f gs
      {|
        gs_flags        := new_flags;
        gs_callstack    := new_xstack;
        gs_regs         := new_regs;
        gs_context_u128 := context_u128;
        gs_pages        := new_pages;
        gs_depot        := depot;
        gs_contracts    := codes;
      |}
.

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

