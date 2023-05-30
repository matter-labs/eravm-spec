From RecordUpdate Require Import RecordSet.
Require SemanticCommon FarCalls.

Import Bool ZArith Common CodeStorage Condition ExecutionStack FarCalls MemoryBase Memory MemoryOps Instruction State ZMod
  ZBits ABI ABI.FarCall ABI.Ret ABI.NearCall ABI.FatPointer Arg Arg.Coercions RecordSetNotations SemanticCommon.


Inductive step_ins: instruction -> state -> state -> Prop :=
(**
<<
## NoOp

Performs no operations.
>>
*)
| step_NoOp:
  forall gs, step_ins OpNoOp gs gs

(**
<<
## ModSP

>>
Performs no operations with memory, but may adjust SP using address modes
[RelSpPop] and [RelSPPush].
*)
| step_ModSP:
  forall codes flags depot pages xstack0 xstack1 new_xstack context_u128 in1 out1 regs,
    resolve_effect__in in1 xstack0 xstack1 ->
    resolve_effect__out out1 xstack1 new_xstack ->
    step_ins (OpModSP in1 out1)
          {|
          gs_callstack    := xstack0;


          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages    := pages;
          gs_depot     := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
          |}
          {|
          gs_callstack    := new_xstack;


          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages    := pages;
          gs_depot     := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
          |}
(**
<<
## Add
Unsigned addition of two numbers.
>>
*)
| step_Add:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_step in1 in2 out mod_swap mod_sf
      (fun x y =>
         let (result, NEW_OF) := x + y in
         let NEW_EQ := EQ_of_bool (result == zero256) in
         let NEW_GT := GT_of_bool (negb NEW_EQ && negb NEW_OF) in
         (result, mk_fs (OF_LT_of_bool NEW_OF) NEW_EQ NEW_GT))
      gs gs' ->

    step_ins (OpAdd in1 in2 out mod_swap mod_sf) gs gs'
(**
<<
## Sub
Unsigned subtraction of two numbers.
>>
 *)

| step_Sub:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_step in1 in2 out mod_swap mod_sf
      (fun x y =>
         let (result, NEW_OF) := x - y in
         let NEW_EQ := EQ_of_bool (result == zero256) in
         let NEW_GT := GT_of_bool (negb NEW_EQ && negb NEW_OF) in
         (result, mk_fs (OF_LT_of_bool NEW_OF) NEW_EQ NEW_GT))
      gs gs' ->

    step_ins (OpSub in1 in2 out mod_swap mod_sf) gs gs'
(**
<<
## And
Bitwise AND of two numbers.
>>
 *)

| step_And:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_step in1 in2 out mod_swap mod_sf
      (fun x y => let result := bitwise_and _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
      gs gs' ->

    step_ins (OpAnd in1 in2 out mod_swap mod_sf) gs gs'
(**
<<
## Or
Bitwise OR of two numbers.
>>
 *)
| step_Or:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_step in1 in2 out mod_swap mod_sf
      (fun x y => let result := bitwise_or _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
      gs gs' ->

    step_ins (OpOr in1 in2 out mod_swap mod_sf) gs gs'

(**
<<
## Xor
Bitwise XOR of two numbers.
>>
 *)
| step_Xor:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_step in1 in2 out mod_swap mod_sf
      (fun x y => let result := bitwise_xor _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
      gs gs' ->

    step_ins (OpXor in1 in2 out mod_swap mod_sf) gs gs'
(**
<<
## Near calls

Calls the code inside the current contract space.

>>
         *)
 | step_NearCall_pass_some_ergs:
    forall codes flags depot pages xstack0 context_u128 regs (abi_params_op:in_reg) abi_params_value call_addr expt_handler ergs_left passed_ergs,

      resolve_fetch_word regs xstack0 pages abi_params_op abi_params_value ->

      Some passed_ergs = option_map NearCall.nca_get_ergs_passed (NearCall.ABI.(decode) abi_params_value) ->

      passed_ergs <> zero32 ->

      (ergs_left, false) = ergs_remaining xstack0 - passed_ergs  ->

      let new_frame := mk_cf expt_handler (sp_get xstack0) call_addr passed_ergs in
      step_ins (OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler))
        {|
          gs_flags        := flags;
          gs_callstack    := xstack0;


          gs_regs         := regs;
          gs_pages    := pages;
          gs_depot     := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := InternalCall new_frame (ergs_set ergs_left xstack0);


          gs_regs         := regs;
          gs_pages    := pages;
          gs_depot     := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}

 | step_NearCall_underflow_pass_all_ergs:
    forall codes flags depot pages xstack0 context_u128 regs (abi_params_op:in_reg) abi_params_value call_addr expt_handler ergs_underflown passed_ergs,
      resolve_fetch_word regs xstack0 pages abi_params_op abi_params_value ->
      Some passed_ergs = option_map NearCall.nca_get_ergs_passed (NearCall.ABI.(decode) abi_params_value) ->
      passed_ergs <> zero32 ->

      (ergs_underflown, true) = ergs_remaining xstack0 - passed_ergs  ->

      let new_frame := mk_cf expt_handler (sp_get xstack0) call_addr (ergs_remaining xstack0) in
      step_ins (OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler))
        {|
          gs_flags        := flags;
          gs_callstack    := xstack0;


          gs_regs         := regs;
          gs_pages    := pages;
          gs_depot     := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := InternalCall new_frame (ergs_reset xstack0);


          gs_regs         := regs;
          gs_pages    := pages;
          gs_depot     := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}

  | step_NearCall_pass_all_ergs:
    forall codes flags depot pages xstack0 xstack1 context_u128 regs (abi_params_op:in_reg) abi_params_value call_addr expt_handler,
      resolve_fetch_word regs xstack0 pages abi_params_op abi_params_value ->

      option_map NearCall.nca_get_ergs_passed  (NearCall.ABI.(decode) abi_params_value)= Some zero32 ->

      let new_frame := mk_cf expt_handler (sp_get xstack0) call_addr (ergs_remaining xstack0) in
      step_ins (OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler))
        {|
          gs_flags        := flags;
          gs_callstack    := xstack0;


          gs_regs         := regs;
          gs_pages    := pages;
          gs_depot     := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}

        {|
          gs_flags        := flags_clear;
          gs_callstack    := InternalCall new_frame (ergs_reset xstack1);


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}

 (**
<<
## Return (normal return, not panic/revert)

>>
  *)
| step_RetLocal_nolabel:
    forall codes flags depot pages cf caller_stack new_caller_stack context_u128 regs _ignored,

      let xstack := InternalCall cf caller_stack in

      ergs_reimburse (ergs_remaining xstack) caller_stack new_caller_stack ->
      step_ins (OpRet _ignored None)
        {|
          gs_flags        := flags;
          gs_callstack    := xstack;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := new_caller_stack;


          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}

| step_RetLocal_label:
  forall gs gs1 _ignored label,
    step_ins (OpRet _ignored None) gs gs1 ->
    step_ins (OpRet _ignored (Some label)) gs (gs1 <| gs_callstack ::= pc_set label |>)



| step_RetExt_ForwardFatPointer:
  forall codes flags depot pages cf caller_stack new_caller_stack context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr shrunk_ptr,
    let xstack0 := ExternalCall cf (Some caller_stack) in
    (* Panic if not a pointer *)
    resolve_fetch_value regs xstack0 pages arg (PtrValue in_ptr_encoded) ->

    Ret.ABI.(decode) in_ptr_encoded = Some (Ret.mk_params in_ptr ForwardFatPointer) ->

    (* Panic if either [page_older] or [validate] do not hold *)
    page_older in_ptr.(fp_page) (get_active_pages xstack0) = false ->

    ergs_reimburse_caller_and_drop xstack0 new_caller_stack ->
    fat_ptr_shrink in_ptr shrunk_ptr ->

    let encoded_shrunk_ptr := FatPointer.ABI.(encode) shrunk_ptr in
    step_ins (OpRet arg label_ignored)
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
                             <| gprs_r1 := PtrValue encoded_shrunk_ptr |>
                             <| gprs_r2 := reg_reserved |>
                             <| gprs_r3 := reg_reserved |>
                             <| gprs_r4 := reg_reserved |> ;
          gs_callstack    := new_caller_stack;
          gs_context_u128 := zero128;


          gs_pages        := pages;
          gs_depot        := depot;
          gs_contracts    := codes;
          |}
(* ------ *)
| step_RetExt_ForwardFatPointer':
  forall codes flags depot pages cf caller_stack new_caller_stack context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr shrunk_ptr,
    let xstack0 := ExternalCall cf (Some caller_stack) in
    let gs := {|
          gs_flags        := flags;
          gs_callstack    := xstack0;
          gs_regs         := regs;
          gs_context_u128 := context_u128;


          gs_pages        := pages;
          gs_depot        := depot;
          gs_contracts    := codes;
          |}  in
    (* Panic if not a pointer *)
    resolve_fetch_value regs xstack0 pages arg (PtrValue in_ptr_encoded) ->

    Ret.ABI.(decode) in_ptr_encoded = Some (Ret.mk_params in_ptr ForwardFatPointer) ->

    (* Panic if either [page_older] or [validate] do not hold *)
    page_older in_ptr.(fp_page) (get_active_pages xstack0) = false ->

    ergs_reimburse_caller_and_drop xstack0 new_caller_stack ->
    fat_ptr_shrink in_ptr shrunk_ptr ->

    let encoded_shrunk_ptr := FatPointer.ABI.(encode) shrunk_ptr in
    step_ins (OpRet arg label_ignored) gs (gs
          <| gs_flags        := flags_clear |>
          <| gs_regs         := regs_state_zero
                             <| gprs_r1 := PtrValue encoded_shrunk_ptr |>
                             <| gprs_r2 := reg_reserved |>
                             <| gprs_r3 := reg_reserved |>
                             <| gprs_r4 := reg_reserved |>  |>
          <| gs_callstack    := new_caller_stack |>
          <| gs_context_u128 := zero128 |>)


(* ------ *)

| step_RetExt_UseHeapOrAuxHeap:
    forall codes flags depot pages cf xstack1 caller_stack new_caller_stack context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr page_id mode current_bound diff,

      let xstack0 := ExternalCall cf (Some caller_stack) in

      (* Panic if not a pointer*)
      resolve_fetch_value regs xstack0 pages arg (IntValue in_ptr_encoded) \/ resolve_fetch_value regs xstack0 pages arg (PtrValue in_ptr_encoded) ->

      Ret.ABI.(decode) in_ptr_encoded = Some (Ret.mk_params in_ptr mode) ->
      (mode = UseHeap \/ mode = UseAuxHeap) ->

      (* Panic if either [page_older] or [validate] does not hold *)
      page_older in_ptr.(fp_page) (get_active_pages xstack0) = false ->
      select_page_bound xstack0 mode (page_id, current_bound) ->
      fat_ptr_induced_growth in_ptr current_bound diff ->
      pay (Ergs.growth_cost diff) xstack0 xstack1 ->

      ergs_reimburse_caller_and_drop xstack1 new_caller_stack ->

      let out_ptr := in_ptr <| fp_page := page_id |> in
      let out_ptr_encoded := FatPointer.ABI.(encode) out_ptr in
      step_ins (OpRet arg label_ignored)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;


          gs_pages    := pages;
          gs_depot     := depot;
          gs_contracts    := codes;
        |}
        {|
          gs_flags        := flags_clear;
          gs_regs         := regs_state_zero
          <| gprs_r1 := PtrValue  out_ptr_encoded |>
          <| gprs_r2 := reg_reserved |>
          <| gprs_r3 := reg_reserved |>
          <| gprs_r4 := reg_reserved |>;
          gs_callstack    := new_caller_stack;
          gs_context_u128 := zero128;


          gs_pages    := pages;
          gs_depot     := depot;
          gs_contracts    := codes;
        |}

(**
<<
## Revert (not return/panic)

>>
  *)

| step_RevertLocal:
  forall gs gs1 _ignored opt_label,
    step_ins (OpRet _ignored opt_label) gs gs1 ->
    let dest := match opt_label with
          | None => active_exception_handler gs.(gs_callstack)
          | Some label => label
          end in
    step_ins (OpRevert _ignored None) gs (gs1 <| gs_callstack ::= pc_set dest |> )

| step_RevertExt_ForwardFatPointer:
  forall codes flags depot pages cf caller_stack new_caller_stack context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr shrunk_ptr,
    let xstack0 := ExternalCall cf (Some caller_stack) in
    (* Panic if not ptr *)
    resolve_fetch_value regs xstack0 pages arg (PtrValue in_ptr_encoded) ->

    Ret.ABI.(decode) in_ptr_encoded = Some( Ret.mk_params in_ptr ForwardFatPointer) ->

    (* Panic if either [page_older] or [validate] do not hold *)
    page_older in_ptr.(fp_page) (get_active_pages xstack0) = false ->

    fat_ptr_shrink in_ptr shrunk_ptr ->
    ergs_reimburse (ergs_remaining xstack0) caller_stack new_caller_stack ->

    let exception_handler := active_exception_handler xstack0 in
    let encoded_shrunk_ptr := FatPointer.ABI.(encode) shrunk_ptr in
    let new_regs := regs_state_zero
          <| gprs_r1 := PtrValue encoded_shrunk_ptr |>
          <| gprs_r2 := reg_reserved |>
          <| gprs_r3 := reg_reserved |>
          <| gprs_r4 := reg_reserved |> in
    step_ins (OpRevert arg label_ignored)
         {|
          gs_flags        := flags;
          gs_callstack    := xstack0;
          gs_regs         := regs;
          gs_context_u128 := context_u128;
          gs_depot        := depot;


          gs_pages        := pages;
          gs_contracts    := codes;
         |}
         {|
          gs_flags        := flags_clear;
          gs_callstack    := pc_set exception_handler new_caller_stack;
          gs_regs         := new_regs;
          gs_context_u128 := zero128;
          gs_depot        := revert_storage cf depot;


          gs_pages        := pages;
          gs_contracts    := codes;
         |}
(**
<<
## Panic (not return/revert)

>>
  *)
| step_PanicLocal:
  forall gs gs1 _ignored opt_label,
    step_ins (OpRevert _ignored opt_label) gs gs1 ->
    step_ins (OpPanic opt_label) gs (gs1 <| gs_flags ::= set_overflow |>)


 | step_PanicExt:
   forall codes flags depot pages cf caller_stack context_u128 regs label_ignored,

     let xstack0 := ExternalCall cf (Some caller_stack) in

     let encoded_res_ptr := FatPointer.ABI.(encode) fat_ptr_empty in
     let new_regs := regs_state_zero
          <| gprs_r1 := PtrValue encoded_res_ptr |>
          <| gprs_r2 := reg_reserved |>
          <| gprs_r3 := reg_reserved |>
          <| gprs_r4 := reg_reserved |> in
     let exception_handler := active_exception_handler xstack0 in
     step_ins (OpPanic label_ignored)
          {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;
          gs_depot        := depot;


          gs_pages        := pages;
          gs_contracts    := codes;
          |}
          {|
          gs_flags        := set_overflow flags_clear;
          gs_regs         := new_regs;
          gs_callstack    := pc_set exception_handler caller_stack;
          gs_context_u128 := zero128;
          gs_depot        := revert_storage cf depot;


          gs_pages        := pages;
          gs_contracts    := codes;
          |}
(**
<<
## Far calls
>>
*)
| step_farcall_normal: forall (handler:imm_in) (abi dest:in_reg) call_as_static dest_addr handler_addr abi_ptr_tag abi_params gs gs',

    fetch_operands abi dest handler (dest_addr, handler_addr, abi_ptr_tag, abi_params)->
    farcall Normal dest_addr handler_addr call_as_static abi_ptr_tag abi_params gs gs' ->

    step_ins (OpFarCall abi dest handler call_as_static) gs gs'

| step_mimic: forall (handler:imm_in) (abi dest:in_reg) call_as_static dest_addr handler_addr abi_ptr_tag abi_params gs gs',

    fetch_operands abi dest handler (dest_addr, handler_addr, abi_ptr_tag, abi_params)->
    farcall Mimic dest_addr handler_addr call_as_static abi_ptr_tag abi_params gs gs' ->

    step_ins (OpMimicCall abi dest handler call_as_static) gs gs'
| step_delegate: forall (handler:imm_in) (abi dest:in_reg) call_as_static dest_addr handler_addr abi_ptr_tag abi_params gs gs',

    fetch_operands abi dest handler (dest_addr, handler_addr, abi_ptr_tag, abi_params)->
    farcall Delegate dest_addr handler_addr call_as_static abi_ptr_tag abi_params gs gs' ->

    step_ins (OpDelegateCall abi dest handler call_as_static) gs gs'
.

Inductive step: state -> state -> Prop :=
   | step_correct:
    forall codes flags depot pages xstack0 xstack1 new_xstack ins context_u128 regs cond new_gs,
      let gs0 := {|
          gs_callstack    := xstack0;

          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages    := pages;
          gs_depot    := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
          |} in
      let gs1 := {|
          gs_callstack    := new_xstack;

          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages    := pages;
          gs_depot     := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
          |} in
      cond_holds cond flags = true ->

      check_requires_kernel ins (is_kernel xstack0) = true ->
      check_allowed_static_ctx ins (topmost_extframe xstack0).(ecf_is_static) = true ->
      fetch_instr regs xstack0 pages (Ins ins cond) ->

      update_pc_regular xstack0 xstack1 ->
      pay (base_cost ins) xstack1 new_xstack ->
      step_ins ins gs1 new_gs ->
      step gs0 new_gs.
