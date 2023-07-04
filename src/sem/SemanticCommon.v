From RecordUpdate Require Import RecordSet.
Require Addressing Common Condition CallStack Memory MemoryContext Instruction State MemoryOps ABI.

Import
  Addressing
    ABI
    ABI.FarCall
    ABI.FatPointer
    ABI.NearCall
    ABI.Ret
    Bool
    Common
    Condition
    CallStack
    Decommitter
    Ergs
    GPR
    Instruction
    Instruction
    List
    ListNotations
    Memory
    MemoryContext
    MemoryBase
    MemoryOps
    Pointer
    PrimitiveValue
    RecordSetNotations
    State
    Storage
    ZArith
    ZBits
    ZMod.

Import Addressing.Coercions.

Section Params.
  Open Scope ZMod_scope.
  Definition MAX_OFFSET_TO_DEREF_LOW_U32: u32 := int_mod_of _ (2^32 - 33)%Z.
End Params.


Inductive update_pc_regular : callstack -> callstack -> Prop :=
| fp_update:
  forall pc' ef,
    let pc := pc_get ef in
    uinc_overflow _ pc = (pc',false) ->
    let ef' := pc_set pc' ef in
    update_pc_regular ef ef'.

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

  Inductive paid_forward: forward_page_type -> fat_ptr * callstack -> fat_ptr * callstack -> Prop :=
  |pf_useheapvariant: forall type in_ptr xstack0 xstack1 query,
      validate_fresh in_ptr = no_exceptions ->
      in_ptr.(fp_start) + in_ptr.(fp_length) = (query, false) ->
      grow_and_pay type query xstack0 xstack1 ->
      paid_forward (UseMemory type) (in_ptr, xstack0) (in_ptr <| fp_page := Some (active_heap_id xstack0) |>, xstack1)
  |pf_forwardfatpointer: forall in_ptr xstack out_ptr,
      validate_non_fresh in_ptr = no_exceptions ->
      fat_ptr_shrink in_ptr out_ptr ->
      paid_forward ForwardFatPointer (in_ptr, xstack) (out_ptr, xstack)
  .

End Payment.

Definition KERNEL_MODE_MAXADDR : contract_address := int_mod_of _ (2^16-1).

Definition addr_is_kernel (addr:contract_address) : bool :=
  lt_unsigned _ addr KERNEL_MODE_MAXADDR.

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



Section UMA.
  Open Scope ZMod_scope.
  (** [word_upper_bound] describes an upper bound expected from heap or auxheap by
a fat pointer. Reading a word from [fp_start + fp_length] requires addresses up
to [fp_start + fp_length + 32] inclusive to be within heap bounds. *)
  Inductive word_upper_bound : fat_ptr -> mem_address -> Prop :=
  | qbu_apply : forall start length addr upper_bound ofs page,
      let bytes_in_word := int_mod_of _ Core.z_bytes_in_word in
      start + length = (addr, false) ->
      addr + bytes_in_word  = (upper_bound, false) ->
      word_upper_bound (mk_fat_ptr page start length ofs) upper_bound.

End UMA.
(** # Helpers *)

Definition smallstep := state -> state -> Prop .
Definition xsmallstep := exec_state -> exec_state -> Prop.
Definition callstack_smallstep := callstack -> callstack -> Prop.
Inductive step_xstate_only (xs1 xs2:exec_state) : smallstep :=
| sxstate_oapply:
  forall gs context_u128,
    step_xstate_only xs1 xs2 {|
                       gs_xstate       := xs1;
                       gs_global       := gs;
                       gs_context_u128 := context_u128;
                     |}
                     {|
                       gs_xstate       := xs2;
                       gs_global       := gs;
                       gs_context_u128 := context_u128;
                     |}.

Inductive step_xstate (S: exec_state -> exec_state -> Prop) : smallstep :=
| sxstate_apply:
  forall xs1 xs2 s1 s2 ,
    S xs1 xs2 ->
    step_xstate_only xs1 xs2 s1 s2->
    step_xstate S s1 s2.

Inductive step_xstate_callstack (S: callstack -> callstack -> Prop) : exec_state -> exec_state -> Prop :=
| scs_apply:
  forall flags regs pages cs1 cs2 xs1 xs2 ,
    S cs1 cs1 ->
    xs1 = {|
            gs_callstack    := cs1;


            gs_flags        := flags;
            gs_regs         := regs;
            gs_pages        := pages;
          |} ->
    xs2 = {|
            gs_callstack    := cs2;


            gs_flags        := flags;
            gs_regs         := regs;
            gs_pages        := pages;
          |} ->

    step_xstate_callstack S xs1 xs2.

Inductive step_callstack (S: callstack -> callstack -> Prop) : smallstep :=
| sc_apply: forall xs1 xs2 s1 s2,
    step_xstate_callstack S xs1 xs1 ->
    step_xstate_only xs1 xs2 s1 s2 ->
    step_callstack S s1 s2.


Generalizable Variables arg out value cs.
Import Addressing.Coercions.
Inductive fetch_apply21:
  (regs_state * memory * callstack) ->
  in_any * primitive_value -> in_any * primitive_value  -> out_any * primitive_value ->
  (regs_state * memory * callstack) ->
  Prop :=

| fa_apply:  forall (arg1:in_any) (arg2:in_any) (out:out_any) result regs0 new_regs mem0 new_mem new_cs,
    `(
        loads _ regs0 cs0 mem0 [(arg1, value1) ; (arg2, value2)] cs1 ->
        store _ regs0 cs1 mem0 out result (new_regs , new_mem, new_cs) ->

        fetch_apply21 (regs0,mem0,cs0)
          (arg1, value1) (arg2, value2) (out, result)
          (new_regs,new_mem,new_cs)
      )
.
Generalizable No Variables.

Generalizable Variables s i o.
Inductive fetch_apply21_swap swap:
  (regs_state * memory * callstack) ->
  in_any * primitive_value -> in_any * primitive_value  -> out_any * primitive_value ->
  (regs_state * memory * callstack) ->
  Prop :=
| fas_apply:
  `(
      apply_swap swap i1 i2 = (i1', i2') ->
      fetch_apply21 s1 i1' i2' o1 s2 ->
      fetch_apply21_swap swap s1 i1 i2 o1 s2
    )
.
Generalizable No Variables.


Generalizable Variables cs regs mem arg value out result.
Inductive fetch_apply22 :
  (regs_state * memory * callstack) ->
  in_any * primitive_value ->
  in_any * primitive_value ->
  out_any * primitive_value ->
  out_any * primitive_value ->
  (regs_state * memory * callstack) -> Prop :=
|fa22_apply: forall new_regs new_mem new_cs,
    `(
        loads _ regs0 cs0 mem0 [(arg1, value1) ; (arg2, value2)] cs1 ->
        stores _ regs0 cs1 mem0 [ (out1, result1); (out2, result2)]
          (new_regs , new_mem, new_cs) ->

        fetch_apply22 (regs0,mem0,cs0)
          (arg1, value1) (arg2, value2) (out1, result1) (out2, result2)
          (new_regs,new_mem,new_cs)
      )
.
Generalizable No Variables.

Generalizable Variables s i o.
Inductive fetch_apply22_swap swap:
  (regs_state * memory * callstack) ->
  in_any * primitive_value -> in_any * primitive_value ->
  out_any * primitive_value ->
  out_any * primitive_value ->
  (regs_state * memory * callstack) ->
  Prop :=
| fas22_apply:
  `(
      apply_swap swap i1 i2 = (i1', i2') ->
      fetch_apply22 s1 i1' i2' o1 o2 s2 ->
      fetch_apply22_swap swap s1 i1 i2 o1 o2 s2
    )
.
Generalizable No Variables.
