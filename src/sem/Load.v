From RecordUpdate Require Import RecordSet.

Require SemanticCommon Addressing.

Import ABI Addressing Bool Common Condition CallStack Memory MemoryOps Instruction State ZMod
  Addressing.Coercions SemanticCommon Pages State RecordSetNotations ZMod.

Import FatPointer.
Import List ListNotations.

Section Defs.
  
  Context (old_regs: regs_state) (old_xstack: callstack) (old_pages:memory).
  Let fetch := resolve_load old_xstack (old_regs, old_pages).
  Let fetch_word := resolve_load_word old_xstack (old_regs,old_pages).
  Let stores := resolve_stores old_xstack (old_regs,old_pages).
  
  Inductive step_load : instruction -> 
                        regs_state * callstack * memory-> Prop :=
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
  .
End Defs.
