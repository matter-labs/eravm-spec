From RecordUpdate Require Import RecordSet.
Require Common Condition Memory Instruction State MemoryOps ABI.

Import Bool ZArith Common CodeStorage Condition MemoryBase Memory MemoryOps Instruction State ZMod
  ZBits ABI ABI.FarCall ABI.Ret ABI.NearCall ABI.FatPointer Arg Arg.Coercions.


Definition reg_reserved := pv0.

Inductive update_pc_regular : execution_frame -> execution_frame -> Prop :=
| fp_update:
  forall pc pc' ef ef',
    fetch_pc ef pc ->
    uinc_overflow _ pc = (pc',false) ->
    update_pc pc' ef ef' ->
    update_pc_regular ef ef'.

Inductive binop_effect: execution_frame -> regs_state -> mem_manager -> flags_state ->
                        in_any -> in_any -> out_any ->
                        mod_swap -> mod_set_flags ->
                        (word_type -> word_type -> (word_type * flags_state)) ->
                        (execution_frame * regs_state * mem_manager * flags_state) -> Prop :=
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

Definition affordable ef (e:ergs): bool :=
 match ergs_remaining ef - e with
   | (paid, false) => true
   | (overflowed, true) => false
 end.

Inductive pay : ergs -> execution_frame -> execution_frame -> Prop :=
  | pay_ergs : forall e ef paid,
      ergs_remaining ef - e = (paid, false) ->
      pay e ef (ergs_set paid ef).

    (* growth_bytes ptr current_bound bytes_grown ->  *)

Inductive pay_growth_or_bankrupt : mem_address -> execution_frame -> execution_frame -> Prop  :=
| phg_affordable: forall ef ef' diff,
    let cost := Ergs.growth_cost diff in
    affordable ef cost = true ->
    pay cost ef ef' ->
    pay_growth_or_bankrupt diff ef ef'
| phg_too_expensive: forall ef ef' diff, 
    let cost := Ergs.growth_cost diff in
    affordable ef cost = false ->
    ef' = ergs_zero ef ->
    pay_growth_or_bankrupt diff ef ef'.


Inductive pay_growth_or_bankrupt_ptr : mem_address -> fat_ptr -> execution_frame -> execution_frame -> Prop  :=
| pgb_ptr:forall current_bound ptr diff ef ef',
    fat_ptr_induced_growth ptr current_bound diff ->
    pay_growth_or_bankrupt diff ef ef' -> 
    pay_growth_or_bankrupt_ptr current_bound ptr ef ef'.

Inductive select_page_bound : execution_frame -> Ret.forward_page_type -> mem_page_id * mem_address -> Prop :=
| fpmspb_heap: forall ef,
    select_page_bound ef UseHeap (active_heap_id ef, (active_mem_ctx ef).(ctx_heap_bound))
| fpmspb_auxheap: forall ef,
    select_page_bound ef UseAuxHeap (active_auxheap_id ef, (active_mem_ctx ef).(ctx_aux_heap_bound)).
