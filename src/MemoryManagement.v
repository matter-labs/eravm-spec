Require CallStack Ergs Memory Pointer.

Import CallStack Common Core Memory MemoryContext Ergs Pointer.

Section MemoryForwarding.
  Open Scope ZMod_scope.

  Context {state_checkpoint: Type} (callstack:=@callstack state_checkpoint).

  (** # Memory forwarding

Contracts communicate by passing each other [%fat_ptr].
Far returns and far calls are able to:

- create them [%ForwardNewFatPointer]
- reuse existing pointers [%ForwardExistingFatPointer].

They chose the action based on an instance of [%fwd_memory] passed through
ABIs. *)
  Inductive fwd_memory :=
    ForwardExistingFatPointer (p:fat_ptr_nullable)
  | ForwardNewFatPointer (heap_var: data_page_type) (s:span).

  (**
- A fat pointer defines a [%slice] of memory and provides a read-only access to it.
- Fat pointers are created from a slice of heap or auxheap of a current contract.
- If the [%span] of a new fat pointer crosses the heap boundary [%heap_variant_bound] then the heap has to grow, and that difference has to be paid for.
- [%growth_query] defines by how much a a heap variant should be grown. *)
  Definition growth_query := @option (prod data_page_type mem_address).

  Definition cost_of_growth (diff:growth_query) : ergs :=
    match diff with
    | Some (_, x) => Ergs.growth_cost x
    | None =>  zero32
    end.

  Inductive growth_to_bound: page_bound -> callstack -> growth_query -> Prop :=
  | goq_grow: forall (hv:data_page_type) (cs: callstack) diff query,
      let current_bound : mem_address := heap_variant_bound cs hv in
      query - current_bound = (false, diff) ->
      growth_to_bound (hv, query) cs (Some (hv, diff))
  | goq_nogrow: forall hv (cs: callstack) __ query,
      let current_bound := heap_variant_bound cs hv in
      query - current_bound = (true, __) ->
      growth_to_bound (hv, query) cs None
  .

  Inductive grow: growth_query -> callstack -> callstack -> Prop :=
  | gr_grow: forall hv cs1 cs2 diff new_apages,
      let apages := get_mem_ctx cs1 in
      grow_heap_variant hv diff apages new_apages ->
      cs2 = update_memory_context new_apages cs1 ->
      grow (Some (hv, diff)) cs1 cs2
  | gr_nogrow: forall cs,
      grow None cs cs.

  Inductive bound_grow_pay: page_bound -> callstack -> callstack -> Prop :=
  | bgp_apply: forall bound query cs1 cs2 cs3,
      growth_to_bound bound cs1 query ->
      pay (cost_of_growth query) cs1 cs2 ->
      grow query cs2 cs3 ->
      bound_grow_pay bound cs1 cs3.

  Inductive span_grow_pay: span -> data_page_type -> callstack -> callstack -> Prop :=
  | sgp_apply: forall s hv cs1 cs2 bound,
      bound_of_span s hv bound ->
      bound_grow_pay bound cs1 cs2 ->
      span_grow_pay s hv cs1 cs2.

  Inductive paid_forward_new_fat_ptr: data_page_type -> span -> callstack -> fat_ptr * callstack -> Prop :=
  | pfnfp_apply: forall s heap_id type cs0 cs1 ,
      span_grow_pay s type cs0 cs1 ->
      heap_id = heap_variant_page_id cs0 type ->
      paid_forward_new_fat_ptr type s cs0 (mk_fat_ptr (Some heap_id) (fresh_ptr s), cs1).

  Inductive growth_to_bound_unaffordable (cs:callstack) bound : Prop :=
    | gtb_apply: forall query,
        growth_to_bound bound cs query ->
        false = affordable cs (cost_of_growth query) ->
        growth_to_bound_unaffordable cs bound.

  Inductive growth_to_span_unaffordable (cs:callstack) heap_type hspan : Prop :=
    | gts_apply: forall bound,
        bound_of_span hspan heap_type bound ->
        growth_to_bound_unaffordable cs bound ->
        growth_to_span_unaffordable cs heap_type hspan.
End MemoryForwarding.
