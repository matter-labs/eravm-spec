(*From RecordUpdate Require Import RecordSet.
Require SemanticAlt.

Import List ListNotations ZArith.
Import ZMod Common MemoryBase Memory MemoryOps Instruction State Semantics.
Import RecordSetNotations.

Definition regs_zero := let z := IntValue zero256 in mk_regs z z z z z z z z z z z z z z z.

Definition regs_init_five_tens :=
let z := IntValue zero256 in
let ten := IntValue (int_mod_of 256 10%Z) in
mk_regs ten ten ten ten ten  z z z z z z z z z z.


Fixpoint add_all_insns (insns: list instruction_predicated) (startaddr: code_address)
  (m: code_page) :=
  match insns with
  | ins :: tail => let m' := store (code_page_params instruction_predicated instruction_invalid) ins startaddr m in
                 let (addr', _) := uinc_overflow _ startaddr in
                 add_all_insns tail addr' m'
  | [] => m
  end.

Definition mk_program_page (insns: list instruction_predicated) :=
  CodePage _ _ (add_all_insns insns zero16 (empty _ )).

Notation no_mods := (mk_cmod NoSwap PreserveFlags).
Import Arg Arg.Coercions.

Definition mem_ctx0 := {|
              ctx_code_page_id := 0; ctx_const_page_id := 0; ctx_stack_page_id := 0; ctx_heap_page_id := 0; ctx_heap_aux_page_id := 0; ctx_heap_bound := zero32; ctx_aux_heap_bound := zero32
            |}.


Definition mod_sp_cf f cf :=
match cf with
 | mk_cf cf_exception_handler_location cf_sp cf_pc cf_ergs =>
     mk_cf cf_exception_handler_location (f cf_sp) cf_pc cf_ergs
 end .

Definition mod_sp f ef :=
  match ef with
  | InternalCall x tail => InternalCall (mod_sp_cf f x) tail
  | ExternalCall x tail => match x with
                          | mk_extcf ecf_this_address ecf_msg_sender
                              ecf_code_address ecf_mem_context ecf_is_static
                              ecf_context_u128_value ecf_saved_storage_state
                              ecx_common =>
                              ExternalCall (mk_extcf ecf_this_address ecf_msg_sender
                                ecf_code_address ecf_mem_context ecf_is_static
                                ecf_context_u128_value ecf_saved_storage_state
                                (mod_sp_cf f ecx_common)) tail
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
          ecx_common := {| cf_exception_handler_location := zero16; cf_sp
                          := zero16; cf_pc := zero16; cf_ergs_remaining := zero32|}
        |} None.

Definition init_state_from (from: list instruction_predicated) :=
  {|
    gs_flags := flags_clear;
    gs_regs := regs_zero;
    gs_contracts := empty contracts_params;
    gs_mem_pages := [ (0, mk_program_page from)];
    gs_callstack := ef0;
    gs_context_u128 := zero128
  |}
.


(*

Theorem noop_reduces:
  forall mods,
  exists s',
    step (init_state_from [Ins (OpNoOp (Reg R0) (Reg R0) (Reg R0) (Reg R0)) mods IfAlways]) s'.
Proof.
  intros [swap sf].
  eexists.
  econstructor; eauto; repeat econstructor; eauto; discriminate.
Qed.


Definition add_prog1 mods :=  [Ins (OpAdd  (Imm (int_mod_of 16 42%Z)) (Reg R1)
                                  (Reg R1)) mods
                 IfAlways].
Theorem add_reduces:
  forall mods,
  exists s',
    step (init_state_from (add_prog1 mods)) s'.
Proof.
  intros [swap sflags].
  unfold add_prog1, init_state_from, ef0, regs_zero, mem_ctx0; simpl.
  destruct swap  eqn:Hsw, sflags eqn:Hsf;
  eexists (Build_global_state
             (if sflags then {| fs_OF_LT := Clear_OF_LT; fs_EQ
                               := Clear_EQ; fs_GT := Set_GT |} else flags_clear)
             (regs_zero <| gprs_r1 := IntValue (int_mod_of 256 42%Z)|>)
             (empty contracts_params)
             (gs_mem_pages (init_state_from (add_prog1 (mk_cmod swap sflags))))
             (pc_mod (fun pc => fst (uinc_overflow _ pc)) ef0)
             zero128
          ) ;
  apply step_Add with (in1 := (Imm (int_mod_of 16 42%Z)))
                                (in2 := Reg R1) (out1:=Reg R1) (cond :=IfAlways)
                                (mod_swap := swap) (mod_sf := sflags)
                                (op1 := (int_mod_of 256 42%Z))
                                (op2 := zero256)
                                (op1' := if swap then zero256 else
                                           (int_mod_of 256 42%Z))
                                (op2' := if swap then (int_mod_of 256 42%Z) else
                                           zero256)
                                (result := (int_mod_of 256 42%Z))
                                (new_OF := false)
                                (xstack1 := ef0);
   subst; try solve [repeat econstructor; discriminate].
Qed.

Definition sub_prog1 mods :=  [Ins (OpSub (Imm (int_mod_of 16 42%Z)) (Reg R1)
                                  (Reg R1)) mods
                 IfAlways].
Theorem sub_reduces:
  forall mods,
  exists s',
    step (init_state_from (sub_prog1 mods)) s'.
Proof.
  intros [swap sflags].
  unfold sub_prog1, init_state_from, ef0, regs_zero, mem_ctx0; simpl.
  destruct swap  eqn:Hsw, sflags eqn:Hsf;
  eexists (Build_global_state
             _
             _
             (empty contracts_params)
             (gs_mem_pages (init_state_from (sub_prog1 (mk_cmod swap sflags))))
             (pc_mod (fun pc => fst (uinc_overflow _ pc)) ef0)
             zero128
          ) ;
  apply step_Sub with (in1 := (Imm (int_mod_of 16 42%Z)))
                                (in2 := Reg R1) (out1:=Reg R1) (cond :=IfAlways)
                                (mod_swap := swap) (mod_sf := sflags)
                                (op1 := int_mod_of 256 42%Z)
                                (op2 := zero256)
                                (op1' := if swap then zero256 else (int_mod_of 256 42%Z))
                                (op2' := if swap then (int_mod_of 256 42%Z) else zero256)
                                (result := if swap then
                                             fst (zero256 - int_mod_of 256 42%Z)
                                           else (int_mod_of 256 42%Z))
                                (new_OF := if swap then true else false)
                                (xstack1 := ef0);
   subst; try solve [repeat econstructor; discriminate].
Qed.

Definition jmp_prog1 mods :=  [Ins (OpJump (Reg R0) ) mods IfAlways].
Theorem jmp_reduces:
  forall sf_mod,
  exists s',
    step (init_state_from (jmp_prog1 (mk_cmod NoSwap sf_mod))) s'.
Proof.
  intros sf_mod.
  destruct sf_mod eqn:Hswap;
  unfold sub_prog1, init_state_from, ef0, regs_zero, mem_ctx0; simpl;
  eexists; econstructor 2; repeat econstructor; discriminate.
Qed.

Definition call_prog1 mods :=  [Ins (OpNearCall (Reg R0) (Imm zero16) (Imm zero16)) mods IfAlways].
Theorem call_reduces:
  forall mods,
  exists s',
    step (init_state_from (call_prog1 mods)) s'.
Proof.
  intros [swap sflags].
  unfold add_prog1, init_state_from, ef0, regs_zero, mem_ctx0; simpl.
  ABI.NearCall.nca_get_ergs_passed
    (ABI.decode ABI.NearCall.params ABI.NearCall.ABI zero256)

  destruct swap  eqn:Hsw, sflags eqn:Hsf; eexists; eapply step_NearCall_underflow_pass_all_ergs
  ; try solve [repeat econstructor].
Qed.
*)
*)
