Require Semantics.

Import List ListNotations ZArith.
Import ZMod Common MemoryBase Memory MemoryOps Instruction State Semantics.

Definition regs_zero := List.repeat (IntValue zero256) 16.

Fixpoint add_all_insns (insns: list instruction) (startaddr: code_address)
  (m: code_page) :=
  match insns with
  | ins :: tail => let m' := store (code_page_params instruction ins_invalid) ins startaddr m in
                 let (addr', _) := uinc_overflow _ startaddr in
                 add_all_insns tail addr' m'
  | [] => m
  end.

Definition mk_program_page (insns: list instruction) :=
  CodePage _ _ (add_all_insns insns zero16 (empty _ )).

Notation no_mods := (mk_cmod NoSwap PreserveFlags).
Import Arg Arg.Coercions.

Definition mem_ctx0 := {|
              ctx_code_page_id := 0; ctx_const_page_id := 0; ctx_stack_page_id := 0; ctx_heap_page_id := 0; ctx_heap_aux_page_id := 0; ctx_heap_bound := zero32; ctx_aux_heap_bound := zero32
            |}.

Definition inc_pc_cf cf :=
match cf with
 | mk_cf cf_exception_handler_location cf_sp cf_pc =>
     let (pc', _) := uinc_overflow _ cf_pc in
     mk_cf cf_exception_handler_location cf_sp pc'
 end .

Definition inc_pc ef :=
  match ef with
  | InternalCall x tail => InternalCall (inc_pc_cf x) tail
  | ExternalCall x tail => match x with
                          | mk_extcf ecf_this_address ecf_msg_sender
                              ecf_code_address ecf_mem_context ecf_is_static
                              ecf_context_u128_value ecf_saved_storage_state
                              ecx_common =>
                              ExternalCall (mk_extcf ecf_this_address ecf_msg_sender
                                ecf_code_address ecf_mem_context ecf_is_static
                                ecf_context_u128_value ecf_saved_storage_state
                                (inc_pc_cf ecx_common)) tail
                          end
 end.

Definition ef0 :=
      ExternalCall
        {|
          ecf_this_address := zero160;
          ecf_msg_sender := zero160;
          ecf_code_address := zero16;
          ecf_mem_context := mem_ctx0 ;
          ecf_is_static := false;
          ecf_context_u128_value := zero128;
          ecf_saved_storage_state := empty storage_params;
          ecx_common := {| cf_exception_handler_location := zero16; cf_sp := zero16; cf_pc := zero16 |}
        |} None.

Definition init_state_from (from: list instruction) :=
  {|
    gs_flags := flags_clear;
    gs_regs := {| rs_gprs := regs_zero |};
    gs_contracts := empty contracts_params;
    gs_mem_pages := [ (0, mk_program_page from)];
    gs_callstack := ef0;
    gs_context_u128 := zero128
  |}
.


(**
Proof that [OpNoOp] reduces.
 *)
Theorem noop_reduces:
  forall mods,
  exists s',
    step (init_state_from [Ins (OpNoOp (Reg R0) (Reg R0) (Reg R0) (Reg R0)) mods IfAlways]) s'.
Proof.
  intros [swap sf].
  eexists.
  econstructor; eauto; repeat econstructor; eauto; discriminate.
Qed.

