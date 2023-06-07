From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import ABI Addressing Bool Common Condition ExecutionStack Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon RecordSetNotations ZArith ZMod.

Import FatPointer.
Import Addressing.Coercions.

Definition MAX_OFFSET_TO_DEREF_LOW_U32: u32 := int_mod_of _ (2^32 - 33)%Z.


Inductive step  : instruction -> smallstep := 

| step_Load:
  forall codes flags depot pages xstack new_xstack context_u128 regs heap_variant ptr_tag enc_ptr (arg_dest:out_reg) (arg_enc_ptr:in_regimm) result new_regs new_pages addr selected_page in_ptr,
    let fetch := resolve_fetch_value regs xstack pages in


    fetch arg_enc_ptr (mk_pv ptr_tag enc_ptr) ->
    ABI.(decode) enc_ptr = Some in_ptr ->
    let used_ptr := in_ptr <| fp_page := heap_variant_id heap_variant xstack |> in

    in_ptr.(fp_offset) <= MAX_OFFSET_TO_DEREF_LOW_U32 = true ->
    
    heap_variant_page heap_variant pages xstack (DataPage _ _ selected_page) ->
    load_data_be_result selected_page addr result ->
    pay_heaps_growth_or_burn heap_variant used_ptr xstack new_xstack ->
    

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
  forall codes flags depot pages xstack new_xstack context_u128 regs heap_variant ptr_tag enc_ptr (arg_dest arg_modptr:out_reg) (arg_enc_ptr:in_regimm) result new_regs new_pages addr selected_page in_ptr out_ptr regs1 pages1,

    resolve_fetch_value regs xstack pages arg_enc_ptr (mk_pv ptr_tag enc_ptr) ->
    ABI.(decode) enc_ptr = Some in_ptr ->
    let used_ptr := in_ptr <| fp_page := heap_variant_id heap_variant xstack |> in

    true = (in_ptr.(fp_offset) <= MAX_OFFSET_TO_DEREF_LOW_U32) ->
    
    heap_variant_page heap_variant pages xstack (DataPage _ _ selected_page) ->
    load_data_be_result selected_page addr result ->
    pay_heaps_growth_or_burn heap_variant used_ptr xstack new_xstack ->
    

    ptr_inc used_ptr out_ptr ->
    resolve_store regs new_xstack pages arg_dest (IntValue result) (regs1, pages1) ->
    resolve_store regs1 new_xstack pages1 arg_modptr (PtrValue (ABI.(encode) out_ptr)) (new_regs, new_pages) ->

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
  forall codes flags depot pages xstack context_u128 regs enc_ptr (arg_dest arg_modptr:out_reg) (arg_enc_ptr:in_reg) result new_regs new_pages addr selected_page in_ptr out_ptr regs1 pages1,

    resolve_fetch_value regs xstack pages arg_enc_ptr (PtrValue enc_ptr) ->
    ABI.(decode) enc_ptr = Some in_ptr ->

    validate_in_bounds in_ptr = true ->
    
    page_has_id pages in_ptr.(fp_page) (DataPage _ _ selected_page) ->
    load_data_be_result selected_page addr result ->
    

    ptr_inc in_ptr out_ptr ->
    resolve_store regs xstack pages arg_dest (IntValue result) (regs1, pages1) ->
    resolve_store regs1 xstack pages1 arg_modptr (PtrValue (ABI.(encode) out_ptr)) (new_regs, new_pages) ->

    step (OpLoadPointerInc arg_enc_ptr arg_dest arg_modptr)
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
           gs_callstack    := xstack;
           gs_pages        := new_pages;


           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}

| step_LoadPointer:
  forall codes flags depot pages xstack context_u128 regs enc_ptr (arg_dest:out_reg) (arg_enc_ptr:in_reg) result new_regs new_pages addr selected_page in_ptr ,

    resolve_fetch_value regs xstack pages arg_enc_ptr (PtrValue enc_ptr) ->
    ABI.(decode) enc_ptr = Some in_ptr ->

    validate_in_bounds in_ptr = true ->

    page_has_id pages in_ptr.(fp_page) (DataPage _ _ selected_page) ->
    load_data_be_result selected_page addr result ->

    resolve_store regs xstack pages arg_dest (IntValue result) (new_regs, new_pages) ->

    step (OpLoadPointer arg_enc_ptr arg_dest)
         {|
           gs_regs         := regs;
           gs_pages        := pages;


           gs_callstack    := xstack;
           gs_flags        := flags;
           gs_depot        := depot;
           gs_context_u128 := context_u128;
           gs_contracts    := codes;
         |}
         {|
           gs_regs         := new_regs;
           gs_pages        := new_pages;


           gs_callstack    := xstack;
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
