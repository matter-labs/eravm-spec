Require CallStack Ergs Memory Pointer.

Import CallStack Common Core Memory MemoryContext Ergs Pointer.

Section MemoryForwarding.
  Import ZMod.
  Open Scope ZMod_scope.

  Context {state_checkpoint: Type} (callstack:=@callstack state_checkpoint).

  Inductive fwd_memory :=
    ForwardExistingFatPointer (p:fat_ptr)
  | ForwardNewFatPointer (heap_var: data_page_type) (s:span).

  Definition growth_query := @option (prod data_page_type mem_address).

  Definition cost_of_growth (diff:growth_query) : ergs :=
    match diff with
    | Some (_, x) => Ergs.growth_cost x
    | None =>  zero32
    end.

  Inductive growth_to_bound: page_bound -> callstack -> growth_query -> Prop :=
  | goq_grow: forall (hv:data_page_type) (cs: callstack) diff query,
      let current_bound : mem_address := heap_variant_bound cs hv in
      query - current_bound = (diff, false) ->
      growth_to_bound (hv, query) cs (Some (hv, diff))
  | goq_nogrow: forall hv (cs: callstack) __ query,
      let current_bound := heap_variant_bound cs hv in
      query - current_bound = (__, true) ->
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
End MemoryForwarding.
