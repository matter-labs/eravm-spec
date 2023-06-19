From RecordUpdate Require Import RecordSet.

Require SemanticCommon Addressing.


Import ABI Addressing Bool Common Condition CallStack Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon Pages State RecordSetNotations ZArith ZMod.

Import FatPointer.
Import List ListNotations.
Import Addressing.Coercions.


Section Defs.
  
  Context (old_regs: regs_state) (old_xstack: callstack) (old_pages:pages).
  Let fetch := resolve_load old_xstack (old_regs, old_pages).
  Let fetch_word := resolve_load_word old_xstack (old_regs, old_pages).
  Let stores := resolve_stores old_xstack (old_regs,old_pages).
  
  Inductive step_load : instruction -> 
                        regs_state * callstack * pages -> Prop :=
  | step_Load:
    forall new_xstack heap_variant enc_ptr (arg_dest:out_reg) (arg_enc_ptr:in_regimm) result new_regs new_pages selected_page in_ptr query,
      fetch_word arg_enc_ptr enc_ptr ->
      ABI.(decode) enc_ptr = Some in_ptr ->
      let used_ptr := in_ptr <| fp_page := heap_variant_id heap_variant old_xstack |> in

      (* In Heap/Auxheap, 'start' of the pointer is always 0, so offset = absolute address *)
      let addr := used_ptr.(fp_offset) in
      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
      
      heap_variant_page _ heap_variant old_pages old_xstack (DataPage _ selected_page) ->
      load_result BigEndian selected_page addr result ->

      word_upper_bound used_ptr query ->
      grow_and_pay heap_variant query old_xstack new_xstack ->

      stores [
          (OutReg arg_dest, IntValue result)
        ] (new_regs, new_pages) ->

      step_load (OpLoad arg_enc_ptr arg_dest heap_variant)
        (new_regs, new_xstack, new_pages)
        
  | step_LoadInc:
    forall new_xstack heap_variant enc_ptr (arg_dest arg_modptr:out_reg) (arg_enc_ptr:in_regimm) result new_regs new_pages selected_page in_ptr ptr_incremented query,

      fetch_word arg_enc_ptr enc_ptr ->
      ABI.(decode) enc_ptr = Some in_ptr ->
      let used_ptr := in_ptr <| fp_page := heap_variant_id heap_variant old_xstack |> in
      
      (* In Heap/Auxheap, 'start' of the pointer is always 0, so offset = absolute address *)
      let addr := used_ptr.(fp_offset) in
      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
      
      heap_variant_page _ heap_variant old_pages old_xstack (DataPage _ selected_page) ->
      load_result BigEndian selected_page addr result ->

      word_upper_bound used_ptr query ->
      grow_and_pay heap_variant query old_xstack new_xstack ->

      ptr_inc used_ptr ptr_incremented  ->
      let out_ptr_enc := ABI.(encode) used_ptr in

      stores [
          (OutReg arg_dest, IntValue result);
          (OutReg arg_modptr, PtrValue out_ptr_enc)
        ] (new_regs, new_pages) ->

      step_load (OpLoadInc arg_enc_ptr arg_dest heap_variant arg_modptr)
        (new_regs, new_xstack, new_pages)

  .

  
  Inductive step_load_ptr : instruction -> 
                            regs_state * pages -> Prop :=
  | step_LoadPointerInc:
    forall enc_ptr (arg_dest arg_modptr:out_reg) (arg_enc_ptr:in_reg) result new_regs new_pages addr selected_page in_ptr out_ptr slice,

      fetch arg_enc_ptr (PtrValue enc_ptr) ->
      ABI.(decode) enc_ptr = Some in_ptr ->

      validate_in_bounds in_ptr = true ->
      
      page_has_id _ old_pages in_ptr.(fp_page) (DataPage  _ selected_page) ->
      slice_from_ptr selected_page in_ptr slice ->
      
      (addr, false) = in_ptr.(fp_start) + in_ptr.(fp_offset) ->
      load_slice_result BigEndian slice addr result ->
      
      ptr_inc in_ptr out_ptr ->

      stores [
          (OutReg arg_dest,    IntValue result);
          (OutReg arg_enc_ptr, PtrValue (ABI.(encode) out_ptr))
        ] (new_regs, new_pages) ->

      step_load_ptr (OpLoadPointerInc arg_enc_ptr arg_dest arg_modptr) (new_regs, new_pages)
                    
  | step_LoadPointer:
    forall enc_ptr (arg_dest: out_reg) (arg_enc_ptr: in_reg) result new_regs new_pages addr selected_page in_ptr slice,

      fetch arg_enc_ptr (PtrValue enc_ptr) ->
      ABI.(decode) enc_ptr = Some in_ptr ->

      validate_in_bounds in_ptr = true ->
      
      page_has_id _ old_pages in_ptr.(fp_page) (DataPage _ selected_page) ->
      slice_from_ptr selected_page in_ptr slice ->
      
      (addr, false) = in_ptr.(fp_start) + in_ptr.(fp_offset) ->
      load_slice_result BigEndian slice addr result ->
      
      stores [
        (OutReg arg_dest, IntValue result)
        ] (new_regs, new_pages) ->

      step_load_ptr (OpLoadPointer arg_enc_ptr arg_dest) (new_regs, new_pages)
  .

  Inductive step_store: instruction -> regs_state * callstack * pages -> Prop :=

  | step_StoreInc:
    forall new_xstack heap_variant enc_ptr (arg_modptr:out_reg) (arg_enc_ptr:in_regimm) (arg_val:in_reg) value new_regs new_pages selected_page in_ptr ptr_incremented pages1 query modified_page,

      let selected_page_id := heap_variant_id heap_variant old_xstack in

      fetch_word arg_enc_ptr enc_ptr ->
      fetch_word arg_val value ->
      
      ABI.(decode) enc_ptr = Some in_ptr ->
      
      let used_ptr := in_ptr <| fp_page := selected_page_id |> in
      
      (* In Heap/Auxheap, 'start' of the pointer is always 0, so offset = absolute address *)
      let addr := used_ptr.(fp_offset) in
      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
      
      heap_variant_page _ heap_variant old_pages old_xstack (DataPage _ selected_page) ->

      word_upper_bound used_ptr query ->
      grow_and_pay heap_variant query old_xstack new_xstack ->

      
      ptr_inc used_ptr ptr_incremented  ->
      
      stores
        [
          (OutReg arg_modptr, PtrValue (ABI.(encode) ptr_incremented))
        ]
        (new_regs, pages1) ->

      store_word_result BigEndian selected_page addr value modified_page ->
      page_replace _ selected_page_id (DataPage _ modified_page) pages1 new_pages ->

      step_store (OpStoreInc arg_enc_ptr arg_val heap_variant arg_modptr)
        (new_regs, new_xstack, new_pages)
  | step_Store:
    forall new_xstack heap_variant enc_ptr (arg_enc_ptr:in_regimm) (arg_val:in_reg) value new_regs new_pages selected_page in_ptr query modified_page,

      let selected_page_id := heap_variant_id heap_variant old_xstack in

      fetch_word arg_enc_ptr enc_ptr ->
      fetch_word arg_val value ->
      
      ABI.(decode) enc_ptr = Some in_ptr ->
      
      (* In Heap/Auxheap, 'start' of the pointer is always 0, so offset = absolute address *)
      let addr := in_ptr.(fp_offset) in
      addr <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
      
      heap_variant_page _ heap_variant old_pages old_xstack (DataPage _ selected_page) ->

      word_upper_bound in_ptr query ->
      grow_and_pay heap_variant query old_xstack new_xstack ->

      store_word_result BigEndian selected_page addr value modified_page ->

      page_replace _ selected_page_id (DataPage _ modified_page) old_pages new_pages ->

      step_store (OpStore arg_enc_ptr arg_val heap_variant) (new_regs, new_xstack, new_pages)
                 
  .

End Defs. 


Inductive step  : instruction -> smallstep := 

| step_LoadVariant:
  forall gs flags  pages xstack new_xstack context_u128 regs new_regs new_pages ins,
    step_load regs xstack pages ins (new_regs, new_xstack, new_pages) ->
    step ins 
         {|
           gs_regs         := regs;
           gs_callstack    := xstack;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
         {|
           gs_regs         := new_regs;
           gs_callstack    := new_xstack;
           gs_pages        := new_pages;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
| step_StoreVariant:
  forall gs flags  pages xstack new_xstack context_u128 regs new_regs new_pages ins,
    step_store regs xstack pages ins (new_regs, new_xstack, new_pages) ->
    step ins 
         {|
           gs_regs         := regs;
           gs_callstack    := xstack;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
         {|
           gs_regs         := new_regs;
           gs_callstack    := new_xstack;
           gs_pages        := new_pages;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
| step_LoadPtrVariant:
  forall gs flags  pages xstack context_u128 regs new_regs new_pages ins,
    step_load_ptr regs xstack pages ins (new_regs, new_pages) ->
    step ins 
         {|
           gs_regs         := regs;
           gs_callstack    := xstack;
           gs_pages        := pages;


           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;


           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
.

(** If set to [Inc32], the instruction:

   - increments lowest 32 bits of $\mathit{in_1}$ by 32 with overflow check (and panics otherwise).
   - for write operations ([OpStore]): place the incremented value in $\mathit{out_1}$;
   - for read operations ([OpLoad], [OpFatPointerRead]): place the incremented value in $\mathit{out_2}$.
 *)
