From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import ABI Addressing Bool Common Condition ExecutionStack Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations ZArith ZMod.

Import FatPointer.
Import Addressing.Coercions.

Definition MAX_OFFSET_TO_DEREF_LOW_U32: u32 := int_mod_of _ (2^32 - 33)%Z.

Inductive slice_from_ptr (m:data_page) : fat_ptr -> data_slice -> Prop :=
  | sfp_apply:
    forall page start length ofs upper_bound readonly_slice,
    start + length = (upper_bound, false) ->
    slice start upper_bound  m = readonly_slice ->
    slice_from_ptr m (mk_fat_ptr  page start length ofs) readonly_slice.


Inductive query_bound_uma : fat_ptr -> mem_address -> Prop :=
  | qbu_apply : forall start length addr upper_bound ofs page,
      let bytes_in_word := int_mod_of _ z_bytes_in_word in
      start + length = (addr, false) ->
      addr + bytes_in_word  = (upper_bound, false) ->
      query_bound_uma (mk_fat_ptr page start length ofs) upper_bound.



Inductive step  : instruction -> smallstep := 

| step_Load:
  forall codes flags depot pages xstack new_xstack context_u128 regs heap_variant ptr_tag enc_ptr (arg_dest:out_reg) (arg_enc_ptr:in_regimm) result new_regs new_pages selected_page in_ptr query,
    let fetch := resolve_fetch_value regs xstack pages in


    fetch arg_enc_ptr (mk_pv ptr_tag enc_ptr) ->
    ABI.(decode) enc_ptr = Some in_ptr ->
    let used_ptr := in_ptr <| fp_page := heap_variant_id heap_variant xstack |> in

    (* In Heap/Auxheap, 'start' of the pointer is always 0, so offset = absolute address *)
    let addr := used_ptr.(fp_offset) in
    addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
    
    heap_variant_page heap_variant pages xstack (DataPage _ _ selected_page) ->
    load_result BigEndian selected_page addr result ->

    query_bound_uma used_ptr query ->
    grow_and_pay heap_variant query xstack new_xstack ->

    resolve_store regs new_xstack pages arg_dest (IntValue result) (new_regs, new_pages) ->

    step (OpLoad arg_enc_ptr arg_dest heap_variant)
         {|
           gs_regs         := regs;
           gs_callstack    := xstack;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_callstack    := new_xstack;
           gs_pages        := new_pages;


           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
        
| step_LoadInc:
  forall codes flags depot pages xstack new_xstack context_u128 regs heap_variant ptr_tag enc_ptr (arg_dest arg_modptr:out_reg) (arg_enc_ptr:in_regimm) result new_regs new_pages selected_page in_ptr ptr_incremented regs1 pages1 query,

    let fetch := resolve_fetch_value regs xstack pages in


    fetch arg_enc_ptr (mk_pv ptr_tag enc_ptr) ->
    ABI.(decode) enc_ptr = Some in_ptr ->
    let used_ptr := in_ptr <| fp_page := heap_variant_id heap_variant xstack |> in
    (* In Heap/Auxheap, 'start' of the pointer is always 0, so offset = absolute address *)
    let addr := used_ptr.(fp_offset) in
    addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
    
    heap_variant_page heap_variant pages xstack (DataPage _ _ selected_page) ->
    load_result BigEndian selected_page addr result ->

    query_bound_uma used_ptr query ->
    grow_and_pay heap_variant query xstack new_xstack ->

    resolve_store regs new_xstack pages arg_dest (IntValue result) (new_regs, new_pages) ->

    ptr_inc used_ptr ptr_incremented  ->
    let out_ptr_enc := PtrValue (ABI.(encode) used_ptr) in
    resolve_store regs new_xstack pages arg_dest (IntValue result) (regs1, pages1) ->
    resolve_store regs1 new_xstack pages1 arg_modptr out_ptr_enc  (new_regs, new_pages) ->

    step (OpLoadInc arg_enc_ptr arg_dest heap_variant arg_modptr)
         {|
           gs_regs         := regs;
           gs_callstack    := xstack;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_callstack    := new_xstack;
           gs_pages        := new_pages;


           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
| step_LoadPointerInc:
  forall codes flags depot pages xstack context_u128 regs enc_ptr (arg_dest arg_modptr:out_reg) (arg_enc_ptr:in_reg) result new_regs new_pages addr selected_page in_ptr out_ptr regs1 pages1 slice,

    resolve_fetch_value regs xstack pages arg_enc_ptr (PtrValue enc_ptr) ->
    ABI.(decode) enc_ptr = Some in_ptr ->

    validate_in_bounds in_ptr = true ->
    
    page_has_id pages in_ptr.(fp_page) (DataPage _ _ selected_page) ->
    slice_from_ptr selected_page in_ptr slice ->
    
    (addr, false) = in_ptr.(fp_start) + in_ptr.(fp_offset) ->
    load_slice_result BigEndian slice addr result ->
    
    ptr_inc in_ptr out_ptr ->
    resolve_store regs xstack pages arg_dest (IntValue result) (regs1, pages1) ->
    resolve_store regs1 xstack pages1 arg_modptr (PtrValue (ABI.(encode) out_ptr)) (new_regs, new_pages) ->

    step (OpLoadPointerInc arg_enc_ptr arg_dest arg_modptr)
         {|
           gs_regs         := regs;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_callstack    := xstack;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;

           gs_flags        := flags;
           gs_callstack    := xstack;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}

| step_LoadPointer:
  forall codes flags depot pages xstack context_u128 regs enc_ptr (arg_dest:out_reg) (arg_enc_ptr:in_reg) result new_regs new_pages addr selected_page in_ptr slice,

    resolve_fetch_value regs xstack pages arg_enc_ptr (PtrValue enc_ptr) ->
    ABI.(decode) enc_ptr = Some in_ptr ->

    validate_in_bounds in_ptr = true ->
    
    page_has_id pages in_ptr.(fp_page) (DataPage _ _ selected_page) ->
    slice_from_ptr selected_page in_ptr slice ->
    
    (addr, false) = in_ptr.(fp_start) + in_ptr.(fp_offset) ->
    load_slice_result BigEndian slice addr result ->
    
    resolve_store regs xstack pages arg_dest (IntValue result) (new_regs, new_pages) ->

    step (OpLoadPointer arg_enc_ptr arg_dest)
         {|
           gs_regs         := regs;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_callstack    := xstack;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;

           gs_flags        := flags;
           gs_callstack    := xstack;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
| step_StoreInc:
  forall codes flags depot pages xstack new_xstack context_u128 regs heap_variant enc_ptr (arg_modptr:out_reg) (arg_enc_ptr:in_regimm) (arg_val:in_reg) value new_regs new_pages selected_page in_ptr ptr_incremented regs1 pages1 query modified_page,

    let selected_page_id := heap_variant_id heap_variant xstack in
    let fetch := resolve_fetch_word regs xstack pages in

    fetch arg_enc_ptr enc_ptr ->
    fetch arg_val value ->
    
    ABI.(decode) enc_ptr = Some in_ptr ->
    
    let used_ptr := in_ptr <| fp_page := selected_page_id |> in
    (* In Heap/Auxheap, 'start' of the pointer is always 0, so offset = absolute address *)
    let addr := used_ptr.(fp_offset) in
    addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
    
    heap_variant_page heap_variant pages xstack (DataPage _ _ selected_page) ->

    query_bound_uma used_ptr query ->
    grow_and_pay heap_variant query xstack new_xstack ->

    store_word_result BigEndian selected_page addr value modified_page ->

    page_replace selected_page_id (DataPage _ _ modified_page) pages pages1 ->
    
    ptr_inc used_ptr ptr_incremented  ->
    let out_ptr_enc := PtrValue (ABI.(encode) ptr_incremented) in
    resolve_store regs1 new_xstack pages1 arg_modptr out_ptr_enc  (new_regs, new_pages) ->

    step (OpStoreInc arg_enc_ptr arg_val heap_variant arg_modptr)
         {|
           gs_regs         := regs;
           gs_callstack    := xstack;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_callstack    := new_xstack;
           gs_pages        := new_pages;


           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
| step_Store:
  forall codes flags depot pages xstack new_xstack context_u128 regs heap_variant enc_ptr (arg_modptr:out_reg) (arg_enc_ptr:in_regimm) (arg_val:in_reg) value new_regs new_pages selected_page in_ptr query modified_page,

    let selected_page_id := heap_variant_id heap_variant xstack in
    let fetch := resolve_fetch_word regs xstack pages in

    fetch arg_enc_ptr enc_ptr ->
    fetch arg_val value ->
    
    ABI.(decode) enc_ptr = Some in_ptr ->
    
    (* In Heap/Auxheap, 'start' of the pointer is always 0, so offset = absolute address *)
    let addr := in_ptr.(fp_offset) in
    addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
    
    heap_variant_page heap_variant pages xstack (DataPage _ _ selected_page) ->

    query_bound_uma in_ptr query ->
    grow_and_pay heap_variant query xstack new_xstack ->

    store_word_result BigEndian selected_page addr value modified_page ->

    page_replace selected_page_id (DataPage _ _ modified_page) pages new_pages ->

    step (OpStore arg_enc_ptr arg_val heap_variant)
         {|
           gs_regs         := regs;
           gs_callstack    := xstack;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_callstack    := new_xstack;
           gs_pages        := new_pages;


           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
.


(** If set to [Inc32], the instruction:

   - increments lowest 32 bits of $\mathit{in_1}$ by 32 with overflow check (and panics otherwise).
   - for write operations ([OpStore]): place the incremented value in $\mathit{out_1}$;
   - for read operations ([OpLoad], [OpFatPointerRead]): place the incremented value in $\mathit{out_2}$.
 *)
