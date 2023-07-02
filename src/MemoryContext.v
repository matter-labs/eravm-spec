From RecordUpdate Require Import RecordSet.

Require Memory lib.ZMod.

Import List Memory ZMod. 

Section Definitions.
  Import ListNotations RecordSetNotations.
  
  Record mem_ctx :=
    mk_mem_ctx
      {
        ctx_code_page_id:  page_id;
        ctx_const_page_id:  page_id;
        ctx_stack_page_id:  page_id;
        ctx_heap_page_id:  page_id;
        ctx_auxheap_page_id:  page_id;
        ctx_heap_bound: mem_address;
        ctx_auxheap_bound: mem_address;
      }.

  Definition list_mem_ctx (ap:mem_ctx) : list page_id :=
    match ap with
    | mk_mem_ctx code_id const_id stack_id heap_id auxheap_id _ _ =>
        [code_id;const_id;stack_id;heap_id;auxheap_id]
    end.
  
  Definition page_older (id: page_id) (mps: mem_ctx) : bool :=
    List.forallb (page_older id) (list_mem_ctx mps).
  Definition is_active_page (ap:mem_ctx) (id: page_id) : bool :=
    List.existsb (page_eq id) (list_mem_ctx ap).

  Open Scope ZMod_scope.
  
  #[export] Instance etaAP: Settable _ := settable! mk_mem_ctx< ctx_code_page_id; ctx_const_page_id; ctx_stack_page_id; ctx_heap_page_id; ctx_auxheap_page_id; ctx_heap_bound; ctx_auxheap_bound >.

  Inductive grow_heap_page: mem_address -> mem_ctx -> mem_ctx -> Prop :=
  | gp_heap: forall ap new_bound diff,
      ap.(ctx_heap_bound) + diff = (new_bound, false) ->
      grow_heap_page diff ap (ap <| ctx_heap_bound := new_bound |>).

  Inductive grow_auxheap_page : mem_address -> mem_ctx -> mem_ctx -> Prop :=
  | gp_auxheap: forall ap new_bound diff,
      ap.(ctx_auxheap_bound) + diff = (new_bound, false) ->
      grow_auxheap_page diff ap (ap <| ctx_auxheap_bound := new_bound |>).

  Inductive grow_heap_variant: data_page_type -> mem_address -> mem_ctx -> mem_ctx -> Prop :=
  | ghv_heap: forall diff ap ap',
      grow_heap_page diff ap ap' ->
      grow_heap_variant Heap diff ap ap'
  | ghv_auxheap: forall diff ap ap',
      grow_auxheap_page diff ap ap' ->
      grow_heap_variant AuxHeap diff ap ap'.

End Definitions.
