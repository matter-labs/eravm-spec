From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Common Condition Ergs Memory Instruction CodeStorage.

Import ZArith Condition Common Ergs MemoryBase Memory CodeStorage Instruction ZMod List ListNotations.


Definition page := page instruction_predicated instruction_invalid.

Definition exception_handler := code_address.

Record callframe_common := mk_cf {
                               cf_exception_handler_location: exception_handler;
                               cf_sp: stack_address;
                               cf_pc: code_address;
                               cf_ergs_remaining: ergs;
                             }.
#[export] Instance etaCFC : Settable _ :=
  settable! mk_cf < cf_exception_handler_location; cf_sp; cf_pc; cf_ergs_remaining >.

Record callframe_external :=
  mk_extcf {
      ecf_this_address: contract_address;
      ecf_msg_sender: contract_address;
      ecf_code_address: code_address;
      ecf_pages: active_pages;
      ecf_is_static: bool; (* forbids any write-like "logs" and so state modifications, event emissions, etc *)
      ecf_context_u128_value: u128;
      ecf_saved_storage_state: storage_type;
      ecf_common :> callframe_common
    }.

#[export] Instance etaCFE : Settable _ :=
  settable! mk_extcf < ecf_this_address; ecf_msg_sender; ecf_code_address; ecf_pages; ecf_is_static; ecf_context_u128_value; ecf_saved_storage_state; ecf_common>.

Inductive callframe :=
| InternalCall (_: callframe_common) (tail: callframe): callframe
| ExternalCall (_: callframe_external) (tail: option callframe): callframe.

Definition execution_stack := callframe.

Definition cfc (ef: callframe) : callframe_common :=
  match ef with
  | InternalCall x _ => x
  | ExternalCall x _ => x
  end.

Definition cfc_map (f:callframe_common->callframe_common) (ef: callframe) : callframe :=
  match ef with
  | InternalCall x tail => InternalCall (f x) tail
  | ExternalCall x tail => ExternalCall (x <| ecf_common ::= f |>) tail
  end.

Definition active_exception_handler (ef: callframe) : exception_handler :=
  (cfc ef).(cf_exception_handler_location).


Section Ergs.

  Definition ergs_remaining (ef:callframe) : ergs := (cfc ef).(cf_ergs_remaining).
  Definition ergs_map (f: ergs->ergs) (ef:callframe) : callframe
    := cfc_map (fun x => x <| cf_ergs_remaining ::= f |>) ef.
  Definition ergs_set newergs := ergs_map (fun _ => newergs).

  Inductive ergs_reimburse : ergs -> callframe -> callframe -> Prop :=
  | er_reimburse: forall delta new_ergs ef ef',
      delta + ergs_remaining ef = (new_ergs, false) ->
      ef' = ergs_set new_ergs ef ->
      ergs_reimburse delta ef ef'.


  Inductive ergs_reimburse_caller_and_drop : callframe -> callframe -> Prop
    :=
  |erc_internal: forall caller new_caller cf,
      ergs_reimburse (ergs_remaining (InternalCall cf caller)) caller
        new_caller ->
      ergs_reimburse_caller_and_drop (InternalCall cf caller) new_caller
  |erc_external: forall caller new_caller cf,
      ergs_reimburse (ergs_remaining (ExternalCall cf (Some caller))) caller
        new_caller ->
      ergs_reimburse_caller_and_drop (ExternalCall cf (Some caller)) new_caller.

  Definition ergs_reset := ergs_set zero32.

  Definition affordable ef (e:ergs): bool :=
    match ergs_remaining ef - e with
    | (paid, false) => true
    | (overflowed, true) => false
    end.

  Inductive pay : ergs -> callframe -> callframe -> Prop :=
  | pay_ergs : forall e ef paid,
      ergs_remaining ef - e = (paid, false) ->
      pay e ef (ergs_set paid ef).
End Ergs.


Section SP.
  (** Fetching value of the stack pointer itself. *)
  Definition sp_get (cf: callframe) : stack_address :=
    (cfc cf).(cf_sp).

  Definition sp_mod_extcall (f:stack_address->stack_address) ef :=
    (ef <| ecf_common ::= fun cf => cf <| cf_sp ::=  f |> |>).

  Inductive sp_mod_extcall_spec f: callframe_external -> callframe_external -> Prop :=
  | sme_apply: forall a b c d e g h eh sp pc ergs,
      sp_mod_extcall_spec f (mk_extcf a b c d e g h (mk_cf eh sp pc ergs))
        (mk_extcf a b c d e g h (mk_cf eh (f sp) pc ergs)).

  Theorem sp_mod_extcall_correct:
    forall f ef, sp_mod_extcall_spec f ef (sp_mod_extcall f ef).
  Proof.
    intros f [].
    destruct ecf_common0.
    constructor.
  Qed.

  Definition sp_mod (f:stack_address->stack_address) ef : callframe :=
    match ef with
    | InternalCall x tail => InternalCall (x <| cf_sp ::=  f |>) tail
    | ExternalCall x tail => ExternalCall (sp_mod_extcall f x) tail
    end.

  Definition sp_update new_sp := sp_mod (fun _ => new_sp).

  Inductive sp_mod_spec f : callframe -> callframe -> Prop :=
  | usp_ext:
    forall ecf ecf' tail,
      sp_mod_extcall_spec f ecf ecf' ->
      sp_mod_spec f (ExternalCall ecf tail) (ExternalCall ecf' tail)
  | usp_int:
    forall  eh sp pc ergs tail,
      sp_mod_spec f (InternalCall (mk_cf eh sp pc ergs) tail) (InternalCall (mk_cf eh (f sp) pc ergs) tail).

  Theorem sp_mod_spec_correct f:
    forall ef, sp_mod_spec f ef (sp_mod f ef).
  Proof.
    destruct ef; destruct c; constructor.
    apply sp_mod_extcall_correct.
  Qed.

End SP.


Section PC.
  Definition pc_get (ef: callframe) : code_address :=
    match ef with
    | InternalCall cf _ => cf.(cf_pc)
    | ExternalCall ef tail => ef.(ecf_common).(cf_pc)
    end.

  Definition pc_mod f ef :=
    match ef with
    | InternalCall x tail => InternalCall (x <| cf_pc ::=  f |>) tail
    | ExternalCall x tail => ExternalCall (x <| ecf_common ::= fun cf => cf <| cf_pc ::=  f |> |>) tail
    end.



  Definition pc_inc (pc pc':code_address) := uinc_overflow _ pc = (pc',false).
  Definition pc_set new := pc_mod (fun _ => new).

  Inductive update_pc_cfc : code_address -> callframe_common -> callframe_common
                            -> Prop :=
  | uupdate_pc:
    forall ehl sp ergs pc pc',
      update_pc_cfc pc' (mk_cf ehl sp pc ergs) (mk_cf ehl sp pc' ergs).

  Inductive update_pc_extcall: code_address -> callframe_external -> callframe_external
                               -> Prop :=
  | upe_update:
    forall pc' cf cf' this_address msg_sender code_address pages is_static context_u128_value saved_storage_state,
      update_pc_cfc pc' cf cf' ->
      update_pc_extcall pc'
        (mk_extcf this_address msg_sender code_address pages is_static
           context_u128_value saved_storage_state cf)
        (mk_extcf this_address msg_sender code_address pages is_static
           context_u128_value saved_storage_state cf')
  .

  Inductive update_pc : code_address -> callframe -> callframe -> Prop :=
  | upc_ext:
    forall ecf ecf' tail pc',
      update_pc_extcall pc' ecf ecf' ->
      update_pc pc' (ExternalCall ecf tail) (ExternalCall ecf' tail)
  | upc_int:
    forall pc' cf cf' tail,
      update_pc_cfc pc' cf cf' ->
      update_pc pc' (InternalCall cf tail) (InternalCall cf' tail).

  Theorem update_pc_correct:
    forall ef pc, update_pc pc ef (pc_set pc ef).
  Proof.
    intros [ []|[] ] pc; simpl; [|destruct ecf_common0]; repeat constructor.
  Qed.

End PC.

Section TopmostExternalFrame.

  Fixpoint topmost_extframe (ef : callframe) : callframe_external :=
    match ef with
    | InternalCall _ tail => topmost_extframe tail
    | ExternalCall x tail => x
    end.

  Inductive topmost_extframe_spec : callframe -> callframe_external -> Prop :=
  | te_Top: forall x t, topmost_extframe_spec (ExternalCall x t) x
  | te_Deeper: forall c t f,
      topmost_extframe_spec t f -> topmost_extframe_spec (InternalCall c t) f
  .
  Theorem topmost_extframe_correct:
    forall ef, topmost_extframe_spec ef (topmost_extframe ef).
  Proof.
    induction ef; constructor; auto.
  Qed.


  Fixpoint change_topmost_extframe f (ef:callframe) : callframe :=
    match ef with
    | InternalCall x tail => InternalCall x (change_topmost_extframe f tail)
    | ExternalCall x tail => ExternalCall (f x) tail
    end.

  Inductive change_topmost_extframe_spec f : callframe -> callframe -> Prop :=
  | ct_base: forall cf t,
      change_topmost_extframe_spec f (ExternalCall cf t) (ExternalCall (f cf) t)
  | ct_ind: forall cf t t',
      change_topmost_extframe_spec f t t' ->
      change_topmost_extframe_spec f (InternalCall cf t) (InternalCall cf t')
  .

  Lemma change_topmost_extframe_correct : forall f ef,
      change_topmost_extframe_spec f ef (change_topmost_extframe f ef).
  Proof.
    intros f ef.
    induction ef as [x tail | x tail]; simpl.
    - apply ct_ind; apply IHtail.
    - simpl.
      apply ct_base.
  Qed.

  Definition update_memory_context (ctx:active_pages): callframe -> callframe :=
    change_topmost_extframe (fun ef => ef <| ecf_pages := ctx |> ).

End TopmostExternalFrame.


Section ActivePages.
  Definition get_active_pages (ef: callframe) : active_pages :=
    (topmost_extframe ef).(ecf_pages).

  Definition active_code_id (ef: callframe) : page_id :=
    (get_active_pages ef).(ctx_code_page_id).

  Definition active_stack_id (ef: callframe) : page_id :=
    (get_active_pages ef).(ctx_stack_page_id).

  Definition active_const_id (ef: callframe) : page_id :=
    (get_active_pages ef).(ctx_const_page_id).

  Definition active_heap_id (ef: callframe) : page_id :=
    (get_active_pages ef).(ctx_heap_page_id).

  Definition active_auxheap_id (ef: callframe) : page_id :=
    (get_active_pages ef).(ctx_auxheap_page_id).

End ActivePages.
