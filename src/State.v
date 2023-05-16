From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Common Memory Instruction.

Import ZArith Common MemoryBase Memory Instruction ZMod List ListNotations.


Definition mem_page := mem_page instruction ins_invalid.

Definition exception_handler := code_address.

Definition ergs := u32.

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
      ecf_code_address: code_address; (* TODO check *)
      ecf_mem_context: ctx_mem_pages;
      ecf_is_static: bool; (** forbid any write-like "logs" and so state modifications, event emissions, etc *)
      ecf_context_u128_value: u128;
      ecf_saved_storage_state: storage_type;
      ecx_common :> callframe_common
    }.

#[export] Instance etaCFE : Settable _ :=
  settable! mk_extcf <
      ecf_this_address;
      ecf_msg_sender;
      ecf_code_address;
      ecf_mem_context;
      ecf_is_static;
      ecf_context_u128_value;
      ecf_saved_storage_state;
      ecx_common>.

Inductive execution_frame :=
| InternalCall (_: callframe_common) (tail: execution_frame): execution_frame
| ExternalCall (_: callframe_external) (tail: option execution_frame): execution_frame.

Definition cfc (ef: execution_frame) : callframe_common :=
  match ef with
  | InternalCall x _ => x
  | ExternalCall x _ => x
  end.

Definition cfc_map (f:callframe_common->callframe_common) (ef: execution_frame) : execution_frame :=
  match ef with
  | InternalCall x tail => InternalCall (f x) tail
  | ExternalCall x tail => ExternalCall (x <| ecx_common ::= f |>) tail
  end.

Definition active_exception_handler (ef: execution_frame) : exception_handler :=
  (cfc ef).(cf_exception_handler_location).

Definition ergs_remaining (ef:execution_frame) : ergs := (cfc ef).(cf_ergs_remaining).
Definition ergs_map (f: ergs->ergs) (ef:execution_frame) : execution_frame
  := cfc_map (fun x => x <| cf_ergs_remaining ::= f |>) ef.

Definition ergs_set newergs := ergs_map (fun _ => newergs).

Inductive ergs_reimburse : ergs -> execution_frame -> execution_frame -> Prop :=
  | er_reimburse: forall delta new_ergs ef ef',
      delta + ergs_remaining ef = (new_ergs, false) ->
      ef' = ergs_set new_ergs ef ->
      ergs_reimburse delta ef ef'.

Definition ergs_zero := ergs_set zero32.

(** Fetching value of the stack pointer itself. *)
Inductive fetch_sp : execution_frame -> stack_address -> Prop :=
| fsp_fetch_ext:
  forall (cf:callframe_external) tail (sp_value:stack_address),
    cf_sp cf = sp_value ->
    fetch_sp (ExternalCall cf tail) sp_value
| fsp_fetch_int:
  forall (cf:callframe_common) tail (sp_value:stack_address),
    cf_sp cf = sp_value ->
    fetch_sp (InternalCall cf tail) sp_value
.

Inductive update_sp_cfc : stack_address -> callframe_common -> callframe_common
                          -> Prop :=
  | usc_update:
    forall ehl sp pc ergs sp',
      update_sp_cfc sp' (mk_cf ehl sp pc ergs) (mk_cf ehl sp' pc ergs).

Inductive update_sp_extcall: stack_address -> callframe_external -> callframe_external
                          -> Prop :=
  | usce_update:
    forall sp' cf cf' this_address msg_sender code_address mem_context is_static context_u128_value saved_storage_state cfc,
      update_sp_cfc sp' cf cf' ->
      update_sp_extcall sp'
        (mk_extcf this_address msg_sender code_address mem_context is_static
           context_u128_value saved_storage_state cfc)
        (mk_extcf this_address msg_sender code_address mem_context is_static
           context_u128_value saved_storage_state cf')
       .

Inductive update_sp : stack_address -> execution_frame -> execution_frame -> Prop :=
| usp_ext:
  forall ecf ecf' tail sp',
    update_sp_extcall sp' ecf ecf' ->
    update_sp sp' (ExternalCall ecf tail) (ExternalCall ecf' tail)
| usp_int:
  forall sp' cf cf' tail,
    update_sp_cfc sp' cf cf' ->
    update_sp sp' (InternalCall cf tail) (InternalCall cf' tail).


(** Fetching value of the program counter itself. *)
Inductive fetch_pc : execution_frame -> code_address -> Prop :=
| fpc_fetch_ext:
  forall addr sender ca mc st ctx ss eh sa tail ergs (pc_value:code_address),
    fetch_pc (ExternalCall (mk_extcf addr sender ca mc st ctx ss
                              (mk_cf eh sa pc_value ergs) ) tail) pc_value
| fpc_fetch_int:
  forall eh sa ergs tail (pc_value:code_address),
    fetch_pc (InternalCall (mk_cf eh sa pc_value ergs) tail) pc_value
.

Definition pc_get (ef: execution_frame) : code_address :=
  match ef with
  | InternalCall cf _ => cf.(cf_pc)
  | ExternalCall ef tail => ef.(ecx_common).(cf_pc)
  end.

Definition pc_mod f ef :=
  match ef with
  | InternalCall x tail => InternalCall (x <| cf_pc ::=  f |>) tail
  | ExternalCall x tail => ExternalCall (x <| ecx_common ::= fun cf => cf <| cf_pc ::=  f |> |>) tail
  end.

Definition pc_inc := pc_mod (fun oldpc => fst (uinc_overflow _ oldpc)).
Definition pc_set new := pc_mod (fun _ => new).

Theorem pc_get_correct:
  forall ef, fetch_pc ef (pc_get ef).
Proof.
  intros [ []|[] ]; simpl; [|destruct ecx_common0]; constructor.
Qed.

Inductive update_pc_cfc : code_address -> callframe_common -> callframe_common
                          -> Prop :=
  | upc_update:
    forall ehl sp ergs pc pc',
      update_pc_cfc pc' (mk_cf ehl sp pc ergs) (mk_cf ehl sp pc' ergs).

Inductive update_pc_extcall: code_address -> callframe_external -> callframe_external
                          -> Prop :=
  | upe_update:
    forall pc' cf cf' this_address msg_sender code_address mem_context is_static context_u128_value saved_storage_state,
      update_pc_cfc pc' cf cf' ->
      update_pc_extcall pc'
        (mk_extcf this_address msg_sender code_address mem_context is_static
           context_u128_value saved_storage_state cf)
        (mk_extcf this_address msg_sender code_address mem_context is_static
           context_u128_value saved_storage_state cf')
       .

Inductive update_pc : code_address -> execution_frame -> execution_frame -> Prop :=
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
  intros [ []|[] ] pc; simpl; [|destruct ecx_common0]; repeat constructor.
Qed.




Inductive topmost_extframe : execution_frame -> execution_frame -> Prop :=
| te_Top: forall x t, topmost_extframe (ExternalCall x t) (ExternalCall x t)
| te_Deeper: forall c t f,
    topmost_extframe t f -> topmost_extframe (InternalCall c t) f
.

Definition mem_manager := list (mem_page_id * mem_page).

Inductive mem_page_replace: mem_manager -> mem_page_id -> mem_page -> mem_manager -> Prop :=
 | mm_replace: forall mm h t id page mm' oldpage,
     mm = h ++ (id, oldpage) :: t ->
     mm' = h ++ (id, page)::t ->
     mem_page_replace mm id page mm'.

Record global_state := {
    gs_flags : flags_state;
    gs_regs: regs_state;
    gs_contracts: contract_collection_type;
    (* gs_pending_exception: bool; we can probably store optional here *)
    gs_mem_pages: mem_manager ;
    gs_callstack: execution_frame;
    gs_context_u128: u128;
  }.



(* Inductive active_mem_ctx : global_state -> ctx_mem_pages -> Prop := *)
(* | amc_Extract: forall gs cf ctx tail, *)
(*     topmost_extframe (gs_callstack gs) (ExternalCall cf  tail)  -> *)
(*     ctx = ecf_mem_context cf -> *)
(*     active_mem_ctx gs ctx *)
(* . *)
Inductive active_mem_ctx : execution_frame -> ctx_mem_pages -> Prop :=
| amc_Extract: forall ef cf ctx tail,
    topmost_extframe ef (ExternalCall cf  tail)  ->
    ctx = ecf_mem_context cf ->
    active_mem_ctx ef ctx
.

(* Inductive mem_page_by_id : global_state -> mem_page_id *)
(*                            -> mem_page -> Prop := *)
(* | mpid_select : forall gs id page, *)
(*     List.In (id, page) gs.(gs_mem_pages) -> *)
(*     mem_page_by_id gs id page *)
(* . *)
Inductive mem_page_by_id : mem_manager -> mem_page_id
                           -> mem_page -> Prop :=
| mpid_select : forall mm id page,
    List.In (id, page) mm ->
    mem_page_by_id mm id page
.


(* Inductive active_codepage_id : global_state -> mem_page_id -> Prop := *)
(* | api_active_code_id: forall gs memctx, *)
(*     active_mem_ctx gs memctx -> *)
(*     active_codepage_id gs memctx.(ctx_code_page_id). *)


(* Inductive active_codepage : global_state -> mem_page -> Prop := *)
(* | ap_active_code: forall gs id codepage, *)
(*     active_codepage_id gs id -> *)
(*     mem_page_by_id gs id codepage -> *)
(*     active_codepage gs codepage. *)

(* Inductive active_constpage_id : global_state -> mem_page_id -> Prop := *)
(* | api_active_const_id: forall gs memctx, *)
(*     active_mem_ctx gs memctx -> *)
(*     active_constpage_id gs memctx.(ctx_const_page_id). *)

(* Inductive active_constpage : global_state -> mem_page -> Prop := *)
(* | ap_active_const: forall gs id constpage, *)
(*     active_constpage_id gs id -> *)
(*     mem_page_by_id gs id constpage -> *)
(*     active_constpage gs constpage. *)

(* Inductive active_stackpage_id : global_state -> mem_page_id -> Prop := *)
(* | api_active_stack_id: forall gs memctx, *)
(*     active_mem_ctx gs memctx -> *)
(*     active_stackpage_id gs memctx.(ctx_stack_page_id). *)


(* Inductive active_stackpage : global_state -> mem_page -> Prop := *)
(* | ap_active_stack_page: forall gs id stack, *)
(*     active_stackpage_id gs id -> *)
(*     mem_page_by_id gs id stack -> *)
(*     active_stackpage gs stack. *)



Inductive active_codepage_id : execution_frame -> mem_page_id -> Prop :=
| api_active_code_id:
  forall ef code_page_id const_page_id stack_page_id heap_page_id heap_aux_page_id heap_bound aux_heap_bound ,
    active_mem_ctx ef (Build_ctx_mem_pages code_page_id const_page_id stack_page_id heap_page_id heap_aux_page_id heap_bound aux_heap_bound) ->
    active_codepage_id ef code_page_id
.

Inductive active_codepage : mem_manager -> execution_frame -> mem_page -> Prop :=
| ap_active_code: forall mm ef id codepage,
    active_codepage_id ef id ->
    mem_page_by_id mm id codepage ->
    active_codepage mm ef codepage.

Inductive active_constpage_id : execution_frame -> mem_page_id -> Prop :=
| api_active_const_id:
  forall ef code_page_id const_page_id stack_page_id heap_page_id heap_aux_page_id heap_bound aux_heap_bound ,
    active_mem_ctx ef (Build_ctx_mem_pages code_page_id const_page_id stack_page_id heap_page_id heap_aux_page_id heap_bound aux_heap_bound) ->
    active_constpage_id ef const_page_id
.

Inductive active_constpage : mem_manager -> execution_frame -> mem_page -> Prop :=
| ap_active_const: forall mm ef id constpage,
    active_constpage_id ef id ->
    mem_page_by_id mm id constpage ->
    active_constpage mm ef constpage.

Inductive active_stackpage_id : execution_frame -> mem_page_id -> Prop :=
| api_active_stack_id:
  forall ef code_page_id const_page_id stack_page_id heap_page_id heap_aux_page_id heap_bound aux_heap_bound ,
    active_mem_ctx ef (Build_ctx_mem_pages code_page_id const_page_id stack_page_id heap_page_id heap_aux_page_id heap_bound aux_heap_bound) ->
    active_stackpage_id ef stack_page_id
.


Inductive active_stackpage : mem_manager -> execution_frame -> mem_page -> Prop :=
| ap_active_stack_page: forall ef mm id stack,
    active_stackpage_id ef id ->
    mem_page_by_id mm id stack ->
    active_stackpage mm ef stack.

Inductive active_heappage_id : execution_frame -> mem_page_id -> Prop :=
| api_active_heap_id: forall ef memctx,
    active_mem_ctx ef memctx ->
    active_heappage_id ef memctx.(ctx_heap_page_id).


Inductive active_heappage : mem_manager -> execution_frame -> mem_page -> Prop :=
| ap_active_heap_page: forall ef mm id heap,
    active_heappage_id ef id ->
    mem_page_by_id mm id heap ->
    active_heappage mm ef heap.

Inductive active_auxheappage_id : execution_frame -> mem_page_id -> Prop :=
| api_active_auxheap_id: forall ef memctx,
    active_mem_ctx ef memctx ->
    active_auxheappage_id ef memctx.(ctx_heap_aux_page_id).


Inductive active_auxheappage : mem_manager -> execution_frame -> mem_page -> Prop :=
| ap_active_auxheap_page: forall ef mm id auxheap,
    active_auxheappage_id ef id ->
    mem_page_by_id mm id auxheap ->
    active_auxheappage mm ef auxheap.


(* Inductive active_heappage_id : global_state -> mem_page_id -> Prop := *)
(* | api_active_heap_id: forall gs memctx, *)
(*     active_mem_ctx gs memctx -> *)
(*     active_heappage_id gs memctx.(ctx_heap_page_id). *)

(* Inductive active_heappage : global_state -> mem_page -> Prop := *)
(* | ap_active_heap: forall gs id heap, *)
(*     active_heappage_id gs id-> *)
(*     mem_page_by_id gs id heap -> *)
(*     active_heappage gs heap. *)

(* Inductive active_auxheappage_id : global_state -> mem_page_id -> Prop := *)
(* | api_active_auxheap_id: forall gs memctx, *)
(*     active_mem_ctx gs memctx -> *)
(*     active_auxheappage_id gs memctx.(ctx_heap_aux_page_id). *)

(* Inductive active_auxheappage : global_state -> mem_page -> Prop := *)
(* | ap_active_auxheap: forall gs id heap, *)
(*     active_auxheappage_id gs id-> *)
(*     mem_page_by_id gs id heap -> *)
(*     active_auxheappage gs heap. *)


Inductive active_page : execution_frame -> mem_page_id -> Prop :=
| api_stack : forall ef id,
    active_stackpage_id ef id ->
    active_page  ef id
| api_code : forall ef id,
    active_codepage_id ef id ->
    active_page  ef id
| api_const : forall ef id,
    active_constpage_id ef id ->
    active_page  ef id
| api_heap : forall ef id,
    active_heappage_id ef id ->
    active_page  ef id
| api_auxheap : forall ef id,
    active_auxheappage_id ef id ->
    active_page  ef id.
