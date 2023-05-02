
Require Common Memory Instruction.

Import ZArith Common MemoryBase Memory Instruction ZMod.


Definition mem_page := mem_page instruction ins_invalid.

(* FIXME *)
Definition exception_handler_location_type := u16.

Record callframe_common := mk_cf {
                               cf_exception_handler_location: exception_handler_location_type;
                               cf_sp_stored: stack_address;
                               cf_pc_stored: code_address;
                             }.

Record callframe_external :=
  mk_extcf {
      ecf_this_address: mem_address;
      ecf_msg_sender: mem_address;
      ecf_code_address: code_address; (* TODO check *)
      ecf_mem_context: ctx_mem_pages;
      ecf_is_static: bool; (** forbid any write-like "logs" and so state modifications, event emissions, etc *)
      ecf_context_u128_value: u128;
      ecf_saved_storage_state: storage_type;
      ecx_common :> callframe_common
    }.

Inductive execution_frame :=
| InternalCall (_: callframe_common) (tail: execution_frame): execution_frame
| ExternalCall (_: callframe_external) (tail: option execution_frame): execution_frame.

Inductive topmost_extframe : execution_frame -> execution_frame -> Prop :=
| te_Top: forall x t, topmost_extframe (ExternalCall x t) (ExternalCall x t)
| te_Deeper: forall c t f,
    topmost_extframe t f -> topmost_extframe (InternalCall c t) f
.

Definition mem_manager := list (mem_page_id * mem_page).
Record global_state := {
    gs_flags : flags_state;
    gs_regs: regs_state;
    gs_contracts: contract_collection_type;
    (* gs_call_or_ret_recently: bool; do we need it? *)
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
| api_active_code_id: forall ef memctx,
    active_mem_ctx ef memctx ->
    active_codepage_id ef memctx.(ctx_code_page_id).


Inductive active_codepage : mem_manager -> execution_frame -> mem_page -> Prop :=
| ap_active_code: forall mm ef id codepage,
    active_codepage_id ef id ->
    mem_page_by_id mm id codepage ->
    active_codepage mm ef codepage.

Inductive active_constpage_id : execution_frame -> mem_page_id -> Prop :=
| api_active_const_id: forall ef memctx,
    active_mem_ctx ef memctx ->
    active_constpage_id ef memctx.(ctx_const_page_id).

Inductive active_constpage : mem_manager -> execution_frame -> mem_page -> Prop :=
| ap_active_const: forall mm ef id constpage,
    active_constpage_id ef id ->
    mem_page_by_id mm id constpage ->
    active_constpage mm ef constpage.

Inductive active_stackpage_id : execution_frame -> mem_page_id -> Prop :=
| api_active_stack_id: forall ef memctx,
    active_mem_ctx ef memctx ->
    active_stackpage_id ef memctx.(ctx_stack_page_id).


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
