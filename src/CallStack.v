From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Common Condition Memory Ergs Log MemoryContext.

Import ZArith Condition Common Ergs Log MemoryBase MemoryContext Memory ZMod List ListNotations.

Section Stack.

  Context (CALLSTACK_LIMIT : nat).
  Context {state_checkpoint: Type} {ins: Type} (ins_invalid: ins)
    (pages := @era_pages _ ins_invalid).
  
  Definition exception_handler := code_address.

  Record callstack_common := mk_cf {
                                 cf_exception_handler_location: exception_handler;
                                 cf_sp: stack_address;
                                 cf_pc: code_address;
                                 cf_ergs_remaining: ergs;
                               }.
  #[export] Instance etaCFC : Settable _ :=
    settable! mk_cf < cf_exception_handler_location; cf_sp; cf_pc; cf_ergs_remaining >.

  Record active_shards := mk_shards {
                              shard_this: shard_id;
                              shard_caller: shard_id;
                              shard_code: shard_id;
                            }.

  #[export] Instance etaSH: Settable _ :=
    settable! mk_shards < shard_this; shard_caller; shard_code>.

  Record callstack_external :=
    mk_extcf {
        ecf_this_address: contract_address;
        ecf_msg_sender: contract_address;
        ecf_code_address: contract_address;
        ecf_mem_ctx: mem_ctx; 
        ecf_is_static: bool; (* forbids any write-like "logs" and so state modifications, event emissions, etc *)
        ecf_context_u128_value: u128;
        ecf_shards:> active_shards;
        ecf_saved_checkpoint: state_checkpoint;
        ecf_common :> callstack_common
      }.

  #[export] Instance etaCFE : Settable _ :=
    settable! mk_extcf < ecf_this_address; ecf_msg_sender; ecf_code_address; ecf_mem_ctx; ecf_is_static; ecf_context_u128_value; ecf_shards; ecf_saved_checkpoint; ecf_common>.

  Inductive callstack :=
  | InternalCall (_: callstack_common) (tail: callstack): callstack
  | ExternalCall (_: callstack_external) (tail: option callstack): callstack.


  Fixpoint callstack_depth cf :=
    (match cf with
     | InternalCall x tail => 1 + callstack_depth tail
     | ExternalCall x (Some tail)=> 1 + callstack_depth tail
     | ExternalCall x None => 1
     end)%nat.

  Definition stack_overflow (xstack:callstack) : bool :=
    Nat.ltb CALLSTACK_LIMIT (callstack_depth xstack).

  Definition cfc (ef: callstack) : callstack_common :=
    match ef with
    | InternalCall x _ => x
    | ExternalCall x _ => x
    end.

  Definition cfc_map (f:callstack_common->callstack_common) (ef: callstack) : callstack :=
    match ef with
    | InternalCall x tail => InternalCall (f x) tail
    | ExternalCall x tail => ExternalCall (x <| ecf_common ::= f |>) tail
    end.


  Section ErgsManagement.

    Import ZMod.
    Open Scope ZMod_scope.
    
    Definition ergs_remaining (ef:callstack) : ergs := (cfc ef).(cf_ergs_remaining).
    Definition ergs_map (f: ergs->ergs) (ef:callstack) : callstack
      := cfc_map (fun x => x <| cf_ergs_remaining ::= f |>) ef.
    Definition ergs_set newergs := ergs_map (fun _ => newergs).

    Inductive ergs_reimburse : ergs -> callstack -> callstack -> Prop :=
    | er_reimburse: forall delta new_ergs ef ef',
        delta + ergs_remaining ef = (new_ergs, false) ->
        ef' = ergs_set new_ergs ef ->
        ergs_reimburse delta ef ef'.


    Inductive ergs_reimburse_caller_and_drop : callstack -> callstack -> Prop
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

    Definition affordable (ef: callstack) (e:ergs): bool :=
      match ergs_remaining ef - e with
      | (paid, false) => true
      | (overflowed, true) => false
      end.

    Inductive pay : ergs -> callstack -> callstack -> Prop :=
    | pay_ergs : forall e ef paid,
        ergs_remaining ef - e = (paid, false) ->
        pay e ef (ergs_set paid ef).
  End ErgsManagement.


  Section SP.
    (** Fetching value of the stack pointer itself. *)
    Definition sp_get (cf: callstack) : stack_address :=
      (cfc cf).(cf_sp).

    Definition sp_mod_extcall (f:stack_address->stack_address) ef :=
      (ef <| ecf_common ::= fun cf => cf <| cf_sp ::=  f |> |>).

    Inductive sp_mod_extcall_spec f: callstack_external -> callstack_external -> Prop :=
    | sme_apply: forall a b c d e g h eh sp pc ss ergs,
        sp_mod_extcall_spec f (mk_extcf a b c d e g h ss (mk_cf eh sp pc ergs))
          (mk_extcf a b c d e g h ss (mk_cf eh (f sp) pc ergs)).

    Theorem sp_mod_extcall_correct:
      forall f ef, sp_mod_extcall_spec f ef (sp_mod_extcall f ef).
    Proof.
      intros f [].
      destruct ecf_common0.
      constructor.
    Qed.

    Definition sp_mod (f:stack_address->stack_address) ef : callstack :=
      match ef with
      | InternalCall x tail => InternalCall (x <| cf_sp ::=  f |>) tail
      | ExternalCall x tail => ExternalCall (sp_mod_extcall f x) tail
      end.

    Definition sp_update new_sp := sp_mod (fun _ => new_sp).

    Inductive sp_mod_spec f : callstack -> callstack -> Prop :=
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
    Definition pc_get (ef: callstack) : code_address :=
      match ef with
      | InternalCall cf _ => cf.(cf_pc)
      | ExternalCall ef tail => ef.(ecf_common).(cf_pc)
      end.

    Definition pc_mod f ef :=
      match ef with
      | InternalCall x tail => InternalCall (x <| cf_pc ::=  f |>) tail
      | ExternalCall x tail => ExternalCall (x <| ecf_common ::= fun cf => cf <| cf_pc ::=  f |> |>) tail
      end.


    Definition pc_set new := pc_mod (fun _ => new).

    Inductive update_pc_cfc : code_address -> callstack_common -> callstack_common
                              -> Prop :=
    | uupdate_pc:
      forall ehl sp ergs pc pc',
        update_pc_cfc pc' (mk_cf ehl sp pc ergs) (mk_cf ehl sp pc' ergs).

    Inductive update_pc_extcall: code_address -> callstack_external -> callstack_external
                                 -> Prop :=
    | upe_update:
      forall pc' cf cf' this_address msg_sender code_address memory is_static context_u128_value saved_storage_state ss,
        update_pc_cfc pc' cf cf' ->
        update_pc_extcall pc'
          (mk_extcf this_address msg_sender code_address memory is_static
             context_u128_value saved_storage_state ss cf)
          (mk_extcf this_address msg_sender code_address memory is_static
             context_u128_value saved_storage_state ss cf')
    .

    Inductive update_pc : code_address -> callstack -> callstack -> Prop :=
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

    Fixpoint topmost_extframe (ef : callstack) : callstack_external :=
      match ef with
      | InternalCall _ tail => topmost_extframe tail
      | ExternalCall x tail => x
      end.

    Inductive topmost_extframe_spec : callstack -> callstack_external -> Prop :=
    | te_Top: forall x t, topmost_extframe_spec (ExternalCall x t) x
    | te_Deeper: forall c t f,
        topmost_extframe_spec t f -> topmost_extframe_spec (InternalCall c t) f
    .
    Theorem topmost_extframe_correct:
      forall ef, topmost_extframe_spec ef (topmost_extframe ef).
    Proof.
      induction ef; constructor; auto.
    Qed.


    Fixpoint change_topmost_extframe f (ef:callstack) : callstack :=
      match ef with
      | InternalCall x tail => InternalCall x (change_topmost_extframe f tail)
      | ExternalCall x tail => ExternalCall (f x) tail
      end.

    Inductive change_topmost_extframe_spec f : callstack -> callstack -> Prop :=
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

    Definition update_memory_context (ctx:mem_ctx): callstack -> callstack :=
      change_topmost_extframe (fun ef => ef <| ecf_mem_ctx := ctx |> ).

    Definition revert_state (ef:callstack_external) : state_checkpoint :=
      ef.(ecf_saved_checkpoint).

    
    Definition current_shard xstack : shard_id := (topmost_extframe xstack).(ecf_shards).(shard_this).

    Definition current_contract xstack : contract_address := (topmost_extframe xstack).(ecf_this_address).

  End TopmostExternalFrame.


  Section ActiveMemory.
    
    Section ActivePageId.

      Context (ef:callstack) (active_extframe := topmost_extframe ef).
     
      
      Definition get_mem_ctx: mem_ctx := (topmost_extframe ef).(ecf_mem_ctx).
      
      Definition active_code_id: page_id := get_mem_ctx.(ctx_code_page_id).
      
      Definition active_stack_id: page_id := get_mem_ctx.(ctx_stack_page_id).
      
      Definition active_const_id: page_id := get_mem_ctx.(ctx_const_page_id).

      Definition active_heap_id : page_id := get_mem_ctx.(ctx_heap_page_id).

      Definition active_auxheap_id : page_id := get_mem_ctx.(ctx_auxheap_page_id).

      Definition heap_bound := get_mem_ctx.(ctx_heap_bound).
      
      Definition auxheap_bound := get_mem_ctx.(ctx_auxheap_bound).
      
    End ActivePageId.
    


    Section ActivePages.
      Context (page_has_id: page_id -> @page pages -> Prop).
      
      Definition active_exception_handler (ef: callstack) : exception_handler :=
        (cfc ef).(cf_exception_handler_location).

      
      Context (ef: callstack) (page_id := fun i => page_has_id (i ef)).
      
      Inductive active_codepage : code_page _ -> Prop :=
      | ap_active_code: forall codepage,
          page_id active_code_id (CodePage codepage) ->
          active_codepage codepage.
      
      Inductive active_constpage : const_page -> Prop :=
      | ap_active_const: forall constpage,
          page_id  active_const_id (ConstPage constpage) ->
          active_constpage  constpage.

      Inductive active_stackpage : stack_page -> Prop :=
      | ap_active_stack: forall  stackpage,
          page_id active_stack_id (StackPage stackpage) ->
          active_stackpage stackpage.

      Inductive active_heappage : data_page -> Prop :=
      | ap_active_heap: forall p,
          page_id active_heap_id (DataPage p) ->
          active_heappage p.

      Inductive active_auxheappage : data_page -> Prop :=
      | ap_active_auxheap: forall p,
          page_id active_auxheap_id (DataPage p) ->
          active_auxheappage p.
    End ActivePages.

  End ActiveMemory.
End Stack.  
