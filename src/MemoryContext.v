From RecordUpdate Require Import RecordSet.

Require Memory lib.ZMod.

Import List Memory ZMod.

Section MemoryContext.
  Import ListNotations RecordSetNotations.

  Open Scope ZMod_scope.

  (** # Memory context

Creation of an external frame leads to allocation of pages for code, constant data, stack, and heap variants.

**Memory context** is a collection of these pages associated with a contract frame, plus the bounds for heap variants.
It is stored in [%ecf_mem_ctx] field of [%ExternalCall] frame.
   *)
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


  (** The exact values of identifiers of pages in [%mem_ctx] are not guaranteed,
  therefore it is not guaranteed that they would be in any particular order.

  However, we need to be able to tell whether a given page was created before a
  given memory context; this is formalized by [%page_older]. *)

  Definition list_mem_ctx (ap:mem_ctx) : list page_id :=
    match ap with
    | mk_mem_ctx code_id const_id stack_id heap_id auxheap_id _ _ =>
        [code_id;const_id;stack_id;heap_id;auxheap_id]
    end.

  Definition page_older (id: page_id) (mps: mem_ctx) : bool :=
    List.forallb (page_older id) (list_mem_ctx mps).

  (** Function [%is_active_page] returns [%true] if memory page [%id] belongs to the context [%c]. *)
  Definition is_active_page (c:mem_ctx) (id: page_id) : bool :=
    List.existsb (page_eq id) (list_mem_ctx c).


  (* begin details: helpers *)
  #[export] Instance etaAP: Settable _ := settable! mk_mem_ctx< ctx_code_page_id; ctx_const_page_id; ctx_stack_page_id; ctx_heap_page_id; ctx_auxheap_page_id; ctx_heap_bound; ctx_auxheap_bound >.
  (* end details *)

  (** If an instruction addresses a heap variant outside of its bounds, its
  bound is adjusted to include the used address. Then the bound has to be
  adjusted; predicates [%grow_heap_page], [%grow_auxheap_page],
  [%grow_heap_variant] are relating memory contexts where an appropriate heap
  variant was grown. *)

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

End MemoryContext.
