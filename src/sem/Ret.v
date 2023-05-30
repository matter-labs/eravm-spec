From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Common Condition ExecutionStack Memory MemoryOps Instruction State ZMod
  ABI ABI.Ret ABI.FatPointer Arg Arg.Coercions SemanticCommon RecordSetNotations.

Inductive paid_forward: forward_page_type -> fat_ptr * execution_stack -> fat_ptr * execution_stack -> Prop :=
|fcf_useheap: forall diff in_ptr xstack0 xstack1,
    let bound := heap_bound xstack0 in
    validate_fresh in_ptr = no_exceptions ->
    fat_ptr_induced_growth in_ptr bound diff ->
    pay_growth_or_burn diff xstack0 xstack1 ->
    paid_forward UseHeap (in_ptr, xstack0) (in_ptr <| fp_page := active_heap_id xstack0 |>, xstack1)

|fcf_useauxheap: forall diff in_ptr xstack0 xstack1,
    let bound := auxheap_bound xstack0 in
    validate_fresh in_ptr = no_exceptions ->
    fat_ptr_induced_growth in_ptr bound diff ->
    pay_growth_or_burn diff xstack0 xstack1 ->
    paid_forward UseAuxHeap (in_ptr, xstack0) (in_ptr <| fp_page := active_heap_id xstack0 |>, xstack1)

|fcf_forwardfatpointer: forall in_ptr xstack out_ptr,
    validate_non_fresh in_ptr = no_exceptions ->
    fat_ptr_shrink in_ptr out_ptr ->
    paid_forward ForwardFatPointer (in_ptr, xstack) (out_ptr, xstack)
.

Inductive step_ret: instruction -> smallstep :=
 (**
<<
## Return (normal return, not panic/revert)

>>
  *)
| step_RetLocal_nolabel:
    forall codes flags depot pages cf caller_stack caller_reimbursed context_u128 regs _ignored,

      ergs_reimburse_caller_and_drop (InternalCall cf caller_stack) caller_reimbursed ->
      step_ret (OpRet _ignored None)
        {|
          gs_flags        := flags;
          gs_callstack    := InternalCall cf caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := caller_reimbursed;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}

| step_RetLocal_label:
  forall gs gs1 _ignored label,
    step_ret (OpRet _ignored None) gs gs1 ->
    step_ret (OpRet _ignored (Some label)) gs (gs1 <| gs_callstack ::= pc_set label |>)

| step_RetExt:
  forall codes flags depot pages cf caller_stack xstack1 caller_reimbursed context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr fwd_mode abi_ptr_tag out_ptr,
    let xstack0 := ExternalCall cf (Some caller_stack) in
    
    (* Panic if not a pointer *)
    resolve_fetch_value regs xstack0 pages arg (mk_pv abi_ptr_tag in_ptr_encoded) ->

    Ret.ABI.(decode) in_ptr_encoded = Some (Ret.mk_params in_ptr fwd_mode) ->

    (fwd_mode = ForwardFatPointer -> abi_ptr_tag = true) ->

    (* Panic if either [page_older] or [validate] do not hold *)
    page_older in_ptr.(fp_page) (get_active_pages xstack0) = false ->

    paid_forward fwd_mode (in_ptr, xstack0) (out_ptr, xstack1) ->
    ergs_reimburse_caller_and_drop xstack1 caller_reimbursed->

    let encoded_out_ptr := FatPointer.ABI.(encode) out_ptr in
    step_ret (OpRet arg label_ignored)
          {|
          gs_flags        := flags;
          gs_callstack    := xstack0;
          gs_regs         := regs;
          gs_context_u128 := context_u128;


          gs_pages        := pages;
          gs_depot        := depot;
          gs_contracts    := codes;
          |}
          {|
          gs_flags        := flags_clear;
          gs_regs         := regs_state_zero
                             <| gprs_r1 := PtrValue encoded_out_ptr |>
                             <| gprs_r2 := reg_reserved |>
                             <| gprs_r3 := reg_reserved |>
                             <| gprs_r4 := reg_reserved |> ;
          gs_callstack    := caller_reimbursed;
          gs_context_u128 := zero128;


          gs_pages        := pages;
          gs_depot        := depot;
          gs_contracts    := codes;
          |}
.


(**
<<
## Revert (not return/panic)

>>
  *)

Inductive step_revert: instruction -> smallstep :=
| step_RevertLocal_nolabel:
    forall codes flags depot pages cf caller_stack caller_reimbursed context_u128 regs _ignored,

      ergs_reimburse_caller_and_drop (InternalCall cf caller_stack) caller_reimbursed ->
      let handler := active_exception_handler (InternalCall cf caller_stack) in
      step_revert (OpRevert _ignored None)
        {|
          gs_flags        := flags;
          gs_callstack    := InternalCall cf caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := pc_set handler caller_reimbursed;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
        
| step_RevertLocal_label:
    forall codes flags depot pages cf caller_stack caller_reimbursed context_u128 regs _ignored label,

      ergs_reimburse_caller_and_drop (InternalCall cf caller_stack) caller_reimbursed ->
      step_revert (OpRevert _ignored (Some label))
        {|
          gs_flags        := flags;
          gs_callstack    := InternalCall cf caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := pc_set label caller_reimbursed;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}


| step_RevertExt:
  forall codes flags depot pages cf caller_stack xstack1 caller_reimbursed context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr fwd_mode abi_ptr_tag out_ptr,
    let xstack0 := ExternalCall cf (Some caller_stack) in
    
    (* Panic if not a pointer *)
    resolve_fetch_value regs xstack0 pages arg (mk_pv abi_ptr_tag in_ptr_encoded) ->
    Ret.ABI.(decode) in_ptr_encoded = Some (Ret.mk_params in_ptr fwd_mode) ->

    (fwd_mode = ForwardFatPointer -> abi_ptr_tag = true) ->

    (* Panic if either [page_older] or [validate] do not hold *)
    page_older in_ptr.(fp_page) (get_active_pages xstack0) = false ->

    paid_forward fwd_mode (in_ptr, xstack0) (out_ptr, xstack1) ->
    ergs_reimburse_caller_and_drop xstack1 caller_reimbursed ->

    let encoded_out_ptr := FatPointer.ABI.(encode) out_ptr in
    step_revert (OpRevert arg label_ignored)
          {|
          gs_flags        := flags;
          gs_callstack    := xstack0;
          gs_regs         := regs;
          gs_context_u128 := context_u128;


          gs_pages        := pages;
          gs_depot        := depot;
          gs_contracts    := codes;
          |}
          {|
          gs_flags        := flags_clear;
          gs_regs         := regs_state_zero
                             <| gprs_r1 := PtrValue encoded_out_ptr |>
                             <| gprs_r2 := reg_reserved |>
                             <| gprs_r3 := reg_reserved |>
                             <| gprs_r4 := reg_reserved |> ;
          gs_callstack    := pc_set (active_exception_handler xstack0) caller_reimbursed ;
          gs_context_u128 := zero128;
          gs_depot        := revert_storage cf depot;


          gs_pages        := pages;
          gs_contracts    := codes;
          |}

.

Inductive step_panic: instruction -> smallstep :=
(**
<<
## Panic (not return/revert)

>>
  *)


| step_PanicLocal_nolabel:
    forall codes flags depot pages cf caller_stack context_u128 regs,

      (* no reimbursement, ergs are lost *)
      let handler := active_exception_handler (InternalCall cf caller_stack) in
      step_panic (OpPanic None)
        {|
          gs_flags        := flags;
          gs_callstack    := InternalCall cf caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
        {|
          gs_flags        := set_overflow flags_clear;
          gs_callstack    := pc_set handler caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
| step_PanicLocal_label:
    forall codes flags depot pages cf caller_stack context_u128 regs _ignored label,

      step_panic (OpRet _ignored (Some label))
        {|
          gs_flags        := flags;
          gs_callstack    := InternalCall cf caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
        {|
          gs_flags        := set_overflow flags_clear;
          gs_callstack    := pc_set label caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}

| step_PanicExt:
  forall codes flags depot pages cf caller_stack context_u128 regs label_ignored (arg:in_reg),
    let xstack0 := ExternalCall cf (Some caller_stack) in
    
    (* Panic if not a pointer *)

    let encoded_out_ptr := FatPointer.ABI.(encode) fat_ptr_empty in
    step_panic (OpPanic label_ignored)
          {|
          gs_flags        := flags;
          gs_callstack    := xstack0;
          gs_regs         := regs;
          gs_context_u128 := context_u128;


          gs_pages        := pages;
          gs_depot        := depot;
          gs_contracts    := codes;
          |}
          {|
          gs_flags        := set_overflow flags_clear;
          gs_regs         := regs_state_zero
                             <| gprs_r1 := PtrValue encoded_out_ptr |>
                             <| gprs_r2 := reg_reserved |>
                             <| gprs_r3 := reg_reserved |>
                             <| gprs_r4 := reg_reserved |> ;
          gs_callstack    := pc_set (active_exception_handler xstack0) caller_stack;
          gs_context_u128 := zero128;
          gs_depot        := revert_storage cf depot;


          gs_pages        := pages;
          gs_contracts    := codes;
          |}

.
