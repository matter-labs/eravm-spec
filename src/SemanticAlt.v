From RecordUpdate Require Import RecordSet.
Require Common Memory Instruction State MemoryOps ABI.

Import Bool ZArith Common MemoryBase Memory MemoryOps Instruction State ZMod
  ZBits ABI ABI.FarCall ABI.Ret ABI.NearCall ABI.FatPointer.

Import RecordSetNotations.
#[export] Instance etaXGS : Settable _ := settable! Build_global_state <gs_flags
  ; gs_regs; gs_contracts ; gs_mem_pages; gs_callstack; gs_context_u128>.

(** * Execution *)

Section Execution.
  Import Arg Arg.Coercions.

  Inductive cond_activated:  cond -> flags_state -> Prop
    :=
  | ac_Always: forall fs,
      cond_activated IfAlways fs

  | ac_GT: forall of_lt eq,
      cond_activated IfGT (mk_fs of_lt eq Set_GT)

  | ac_EQ: forall of_lt gt,
      cond_activated IfEQ (mk_fs of_lt Set_EQ gt)

  | ac_LT: forall eq gt,
      cond_activated IfLT (mk_fs Set_OF_LT eq gt)

  | ac_GE1: forall fs,
      cond_activated IfEQ fs ->
      cond_activated IfGE fs

  | ac_GE2: forall fs,
      cond_activated IfGT fs ->
      cond_activated IfGE fs

  | ac_LE1: forall fs,
      cond_activated IfLT fs ->
      cond_activated IfLE fs
  | ac_LE2: forall fs,
      cond_activated IfEQ fs ->
      cond_activated IfLE fs

  | ac_NotEQ: forall of_lt gt,
      cond_activated IfNotEQ (mk_fs of_lt Clear_EQ gt)

  | ac_IfGTOrLT1: forall fs,
      cond_activated IfGT fs->
      cond_activated IfGTOrLT fs

  | ac_IfGTOrLT2: forall fs,
      cond_activated IfLT fs->
      cond_activated IfGTOrLT fs
  .

  Hint Constructors cond_activated :flags.

  Theorem cond_activated_dec: forall ec flags, Decidability.dec (cond_activated ec flags).
  Proof.
    intros ec flags.
    unfold Decidability.dec.
    destruct ec, flags; destruct fs_OF_LT, fs_EQ, fs_GT;
      solve [left;constructor| right;inversion 1 | auto with flags | right; inversion 1; subst; inversion H0].
  Defined.


  Inductive update_pc_regular : execution_frame -> execution_frame -> Prop :=
  | fp_update:
    forall pc pc' ef ef',
      fetch_pc ef pc ->
      uinc_overflow _ pc = (pc',false) ->
      update_pc pc' ef ef' ->
      update_pc_regular ef ef'.

  Definition apply_swap {T} (md: mod_swap) (a b:T) : T*T :=
    match md with
    | NoSwap => (a,b)
    | Swap => (b,a)
    end.

  Definition apply_set_flags (md: mod_set_flags) (f f':flags_state) : flags_state :=
    match md with
    | SetFlags => f'
    | PreserveFlags => f
    end.

  Definition reg_reserved := pv0.

  Definition set_overflow fs := match fs with
                                | mk_fs _ EQ GT => mk_fs Set_OF_LT EQ GT
                                end.

Inductive binop_effect: execution_frame -> regs_state -> mem_manager -> flags_state ->
                        in_any -> in_any -> out_any ->
                        mod_swap -> mod_set_flags ->
                        (word_type -> word_type -> (word_type * flags_state)) ->
                        (execution_frame * regs_state * mem_manager * flags_state) -> Prop :=
| be_apply:
  forall f ef0 ef1 ef' regs regs' mm mm' (in1 in2: in_any) (out: out_any) loc1 loc2
    op1 op2 op1' op2' swap set_flags out_loc result flags_candidate flags0 new_flags,
    resolve ef0 regs in1 loc1 ->
    resolve_effect__in in1 ef0 ef1 ->
    resolve ef1 regs in2 loc2 ->
    resolve ef1 regs out out_loc ->
    resolve_effect__out out ef1 ef' ->
    fetch_loc regs ef' mm loc1 (FetchPV (IntValue op1)) ->
    fetch_loc regs ef' mm loc2 (FetchPV (IntValue op2)) ->
    apply_swap swap op1 op2 = (op1', op2') ->
    f op1' op2' = (result, flags_candidate) ->
    store_loc regs ef' mm (IntValue result) out_loc (regs', mm') ->
    new_flags = apply_set_flags set_flags flags0 flags_candidate ->
    binop_effect ef0 regs mm flags0 in1 in2 out swap set_flags f (ef', regs', mm', new_flags).


Definition usub_saturate {bits} (x y: int_mod bits) :=
  let (res, underflow) := x - y in
  if underflow then int_mod_of bits 0%Z else res.



Inductive pay_growth : execution_frame -> mem_address -> fat_ptr -> execution_frame -> Prop  :=
| phg_affordable: forall ptr cf tail current_bound bytes_grown paid_growth,
    growth_bytes ptr current_bound bytes_grown ->
    ergs_remaining (ExternalCall cf tail) - Ergs.growth_cost bytes_grown = (paid_growth, false) ->
    pay_growth (ExternalCall cf tail) current_bound ptr (ergs_set paid_growth (ExternalCall cf tail))
| phg_too_expensive: forall ptr cf tail current_bound bytes_grown _overflown,
    growth_bytes ptr current_bound bytes_grown ->
    ergs_remaining (ExternalCall cf tail) - Ergs.growth_cost bytes_grown = (_overflown, true) ->
    pay_growth (ExternalCall cf tail) current_bound ptr (ergs_zero (ExternalCall cf tail))
.

Inductive select_page_bound : execution_frame -> Ret.forward_page_type -> mem_page_id * mem_address -> Prop :=
  | fpmspb_heap: forall ef,
    select_page_bound ef UseHeap (active_heap_id ef, (active_mem_ctx ef).(ctx_heap_bound))
  | fpmspb_auxheap: forall ef,
    select_page_bound ef UseAuxHeap (active_auxheap_id ef, (active_mem_ctx ef).(ctx_aux_heap_bound)).

Inductive step_ins: instruction -> global_state -> global_state -> Prop :=

(*
<<
## NoOp

Performs no operations.
>>
*)
| step_NoOp:
  forall gs, step_ins OpNoOp gs gs

(*
<<
## ModSP

>>
Performs no operations with memory, but may adjust SP using address modes
[RelSpPop] and [RelSPPush].
*)
| step_ModSP:
  forall flags contracts mem_pages xstack0 xstack1 new_xstack context_u128 in1 out1 regs,
    resolve_effect__in in1 xstack0 xstack1 ->
    resolve_effect__out out1 xstack1 new_xstack ->
    step_ins (OpModSP in1 out1)
             {|
               gs_callstack    := xstack0;


               gs_flags        := flags;
               gs_regs         := regs;
               gs_mem_pages    := mem_pages;
               gs_contracts    := contracts;
               gs_context_u128 := context_u128;
             |}
             {|
               gs_callstack    := new_xstack;


               gs_flags        := flags;
               gs_regs         := regs;
               gs_mem_pages    := mem_pages;
               gs_contracts    := contracts;
               gs_context_u128 := context_u128;
             |}
(**
<<
## Add
Unsigned addition of two numbers.
>>
*)
  | step_Add:
    forall flags new_flags mod_swap mod_sf contracts mem_pages new_mem_pages xstack new_xstack context_u128 (in1:in_any) (in2:in_reg) out regs new_regs,

      binop_effect xstack regs mem_pages flags in1 in2 out mod_swap mod_sf
        (fun x y =>
           let (result, NEW_OF) := x + y in
           let NEW_EQ := EQ_of_bool (result == zero256) in
           let NEW_GT := GT_of_bool (negb NEW_EQ && negb NEW_OF) in
           (result, mk_fs (OF_LT_of_bool NEW_OF) NEW_EQ NEW_GT))
        (new_xstack, new_regs, new_mem_pages, new_flags) ->

      step_ins (OpAdd in1 in2 out mod_swap mod_sf)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_callstack    := xstack;


          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := new_flags;
          gs_regs         := new_regs;
          gs_mem_pages    := new_mem_pages;
          gs_callstack    := new_xstack;


          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}
(**
<<
## Sub
Unsigned subtraction of two numbers.
>>
*)

| step_Sub:
    forall flags new_flags mod_swap mod_sf contracts mem_pages new_mem_pages xstack new_xstack context_u128 (in1:in_any) (in2:in_reg) out regs new_regs,

      binop_effect xstack regs mem_pages flags in1 in2 out mod_swap mod_sf
        (fun x y =>
           let (result, NEW_OF) := x - y in
           let NEW_EQ := EQ_of_bool (result == zero256) in
           let NEW_GT := GT_of_bool (negb NEW_EQ && negb NEW_OF) in
           (result, mk_fs (OF_LT_of_bool NEW_OF) NEW_EQ NEW_GT))
        (new_xstack, new_regs, new_mem_pages, new_flags) ->

      step_ins (OpSub in1 in2 out mod_swap mod_sf)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_callstack    := xstack;


          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := new_flags;
          gs_regs         := new_regs;
          gs_mem_pages    := new_mem_pages;
          gs_callstack    := new_xstack;


          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}
(**
<<
## And
Bitwise AND of two numbers.
>>
*)

| step_And:
    forall flags new_flags mod_swap mod_sf contracts mem_pages new_mem_pages xstack new_xstack context_u128 (in1:in_any) (in2:in_reg) out regs new_regs,

      binop_effect xstack regs mem_pages flags in1 in2 out mod_swap mod_sf
        (fun x y => let result := bitwise_and _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
        (new_xstack, new_regs, new_mem_pages, new_flags) ->

      step_ins (OpAnd in1 in2 out mod_swap mod_sf)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_callstack    := xstack;


          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := new_flags;
          gs_regs         := new_regs;
          gs_mem_pages    := new_mem_pages;
          gs_callstack    := new_xstack;


          gs_contracts := contracts;
          gs_context_u128 := context_u128;
        |}
(**
<<
## Or
Bitwise OR of two numbers.
>>
*)
| step_Or:
    forall flags new_flags mod_swap mod_sf contracts mem_pages new_mem_pages xstack new_xstack context_u128 (in1:in_any) (in2:in_reg) out regs new_regs,

      binop_effect xstack regs mem_pages flags in1 in2 out mod_swap mod_sf
        (fun x y => let result := bitwise_or _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
        (new_xstack, new_regs, new_mem_pages, new_flags) ->

      step_ins (OpOr in1 in2 out mod_swap mod_sf)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_callstack    := xstack;


          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := new_flags;
          gs_regs         := new_regs;
          gs_mem_pages    := new_mem_pages;
          gs_callstack    := new_xstack;


          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}

(**
<<
## Xor
Bitwise XOR of two numbers.
>>
*)
| step_Xor:
    forall flags new_flags mod_swap mod_sf contracts mem_pages new_mem_pages xstack new_xstack context_u128 (in1:in_any) (in2:in_reg) out regs new_regs,

      binop_effect xstack regs mem_pages flags in1 in2 out mod_swap mod_sf
        (fun x y => let result := bitwise_or _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
        (new_xstack, new_regs, new_mem_pages, new_flags) ->

      step_ins (OpXor in1 in2 out mod_swap mod_sf)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_callstack    := xstack;


          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := new_flags;
          gs_regs         := new_regs;
          gs_mem_pages    := new_mem_pages;
          gs_callstack    := new_xstack;


          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}

(**
<<
## Near calls

Calls the code inside the current contract space.

>>
         *)
 | step_NearCall_pass_some_regs:
    forall flags contracts mem_pages xstack0 context_u128 regs (abi_params_op:in_reg) abi_params_value call_addr expt_handler ergs_left,

      resolve_fetch_word regs xstack0 mem_pages abi_params_op abi_params_value ->

      let passed_ergs := (NearCall.ABI.(decode) abi_params_value).(NearCall.nca_get_ergs_passed) in
      passed_ergs <> zero32 ->

      (ergs_left, false) = ergs_remaining xstack0 - passed_ergs  ->

      let new_frame := mk_cf expt_handler (sp_get xstack0) call_addr passed_ergs in
      step_ins (OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler))
        {|
          gs_flags        := flags;
          gs_callstack    := xstack0;


          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := InternalCall new_frame (ergs_set ergs_left xstack0);


          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_context_u128 := context_u128;
        |}

 | step_NearCall_underflow_pass_all_regs:
    forall flags contracts mem_pages xstack0 context_u128 regs (abi_params_op:in_reg) abi_params_value call_addr expt_handler ergs_underflown,
      resolve_fetch_word regs xstack0 mem_pages abi_params_op abi_params_value ->
      let passed_ergs := (NearCall.ABI.(decode) abi_params_value).(NearCall.nca_get_ergs_passed) in
      passed_ergs <> zero32 ->

      (ergs_underflown, true) = ergs_remaining xstack0 - passed_ergs  ->

      let new_frame := mk_cf expt_handler (sp_get xstack0) call_addr (ergs_remaining xstack0) in
      step_ins (OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler))
        {|
          gs_flags := flags;
          gs_callstack := xstack0;


          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags_clear;
          gs_callstack := InternalCall new_frame (ergs_zero xstack0);


          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_context_u128 := context_u128;
        |}

  | step_NearCall_pass_all_ergs:
    forall flags contracts mem_pages xstack0 xstack1 context_u128 regs (abi_params_op:in_reg) abi_params_value call_addr expt_handler,
      resolve_fetch_word regs xstack0 mem_pages abi_params_op abi_params_value ->

      (NearCall.ABI.(decode) abi_params_value).(NearCall.nca_get_ergs_passed) = zero32 ->

      let new_frame := mk_cf expt_handler (sp_get xstack0) call_addr (ergs_remaining xstack0) in
      step_ins (OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler))
        {|
          gs_flags := flags;
          gs_callstack := xstack0;


          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_context_u128 := context_u128;
        |}

        {|
          gs_flags := flags_clear;
          gs_callstack := InternalCall new_frame (ergs_zero xstack1);


          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_context_u128 := context_u128;
        |}

 (**
<<
## Return (normal return, not panic/revert)

>>
  *)
| step_RetLocal_nolabel:
    forall flags contracts mem_pages cf caller_stack new_caller_stack context_u128 regs _ignored,

      let xstack := InternalCall cf caller_stack in

      ergs_reimburse (ergs_remaining xstack) caller_stack new_caller_stack ->
      step_ins (OpRet _ignored None)
        {|
          gs_flags        := flags;
          gs_callstack    := xstack;


          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := flags_clear;
          gs_callstack    := new_caller_stack;


          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_context_u128 := context_u128;
        |}

| step_RetLocal_label:
  forall gs gs1 _ignored label,
    step_ins (OpRet _ignored None) gs gs1 ->
    step_ins (OpRet _ignored (Some label)) gs (gs1 <| gs_callstack ::= pc_set label |>)



| step_RetExt_ForwardFatPointer:
  forall flags contracts mem_pages cf caller_stack new_caller_stack context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr shrunk_ptr,
    let xstack0 := ExternalCall cf (Some caller_stack) in
    (* Panic if not a pointer*)
    resolve_fetch_value regs xstack0 mem_pages arg (PtrValue in_ptr_encoded) ->

    Ret.ABI.(decode) in_ptr_encoded = Ret.mk_params in_ptr ForwardFatPointer ->

    (* Panic if either [page_older] or [validate] do not hold *)
    page_older in_ptr.(fp_mem_page) cf.(ecf_mem_context)  = false ->

    ergs_reimburse_caller xstack0 new_caller_stack ->
    fat_ptr_shrink in_ptr shrunk_ptr ->

    let encoded_shrunk_ptr := FatPointer.ABI.(encode) shrunk_ptr in
    let new_regs := regs_state_zero
                      <| gprs_r1 := PtrValue encoded_shrunk_ptr |>
                      <| gprs_r2 := reg_reserved |>
                      <| gprs_r3 := reg_reserved |>
                      <| gprs_r4 := reg_reserved |> in
    step_ins (OpRet arg label_ignored)
             {|
               gs_flags        := flags;
               gs_callstack    := xstack0;
               gs_regs         := regs;


               gs_mem_pages    := mem_pages;
               gs_contracts    := contracts;
               gs_context_u128 := context_u128;
             |}
             {|
               gs_flags        := flags_clear;
               gs_regs         := new_regs;
               gs_callstack    := new_caller_stack;


               gs_mem_pages    := mem_pages;
               gs_contracts    := contracts;
               gs_context_u128 := zero128;
             |}

| step_RetExt_UseHeapOrAuxHeap:
    forall flags contracts mem_pages cf xstack1 caller_stack new_caller_stack context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr page_id mode current_bound,

      let xstack0 := ExternalCall cf (Some caller_stack) in

      (* Panic if not a pointer*)
      resolve_fetch_value regs xstack0 mem_pages arg (PtrValue in_ptr_encoded) ->

      Ret.ABI.(decode) in_ptr_encoded = Ret.mk_params in_ptr mode ->
      (mode = UseHeap \/ mode = UseAuxHeap) ->

      (* Panic if either [page_older] or [validate] does not hold *)
      page_older in_ptr.(fp_mem_page) cf.(ecf_mem_context)  = false ->
      select_page_bound xstack0 mode (page_id, current_bound) ->
      pay_growth xstack0 current_bound in_ptr xstack1 ->

      ergs_reimburse_caller xstack1 new_caller_stack ->

      let out_ptr := in_ptr <| fp_mem_page := page_id |> in
      let out_ptr_encoded := FatPointer.ABI.(encode) out_ptr in
      step_ins (OpRet arg label_ignored)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;


          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
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


          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
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
  forall flags contracts mem_pages cf caller_stack new_caller_stack context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr shrunk_ptr,
    let xstack0 := ExternalCall cf (Some caller_stack) in
    (* Panic if not ptr *)
    resolve_fetch_value regs xstack0 mem_pages arg (PtrValue in_ptr_encoded) ->

    Ret.ABI.(decode) in_ptr_encoded = Ret.mk_params in_ptr ForwardFatPointer ->

    (* Panic if either [page_older] or [validate] do not hold *)
    page_older in_ptr.(fp_mem_page) cf.(ecf_mem_context)  = false ->

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


               gs_mem_pages    := mem_pages;
               gs_contracts    := contracts;
             |}
             {|
               gs_flags        := flags_clear;
               gs_callstack    := pc_set exception_handler new_caller_stack;
               gs_regs         := new_regs;
               gs_context_u128 := zero128;


               gs_mem_pages    := mem_pages;
               gs_contracts    := contracts;
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


(* FIXME suspicious; *)
(* | step_PanicExt_ForwardFatPointer: *)
(*   forall flags contracts mem_pages cf caller_stack new_caller_stack context_u128 regs label_ignored, *)

(*       let xstack0 := ExternalCall cf (Some caller_stack) in *)

(*       resolve_fetch_value regs xstack0 mem_pages arg (PtrValue in_ptr_encoded) -> *)
(*       Ret.ABI.(decode) in_ptr_encoded = Ret.mk_params in_ptr ForwardFatPointer -> *)

(*       ergs_reimburse (ergs_remaining xstack0) caller_stack new_caller_stack -> *)
(*       let encoded_res_ptr := FatPointer.ABI.(encode) fat_ptr_empty in *)
(*       let new_regs := regs_state_zero *)
(*                         <| gprs_r1 := PtrValue encoded_res_ptr |> *)
(*                         <| gprs_r2 := reg_reserved |> *)
(*                         <| gprs_r3 := reg_reserved |> *)
(*                         <| gprs_r4 := reg_reserved |> in *)
(*       let exception_handler := active_exception_handler xstack0 in *)
(*       step_ins (OpPanic label_ignored) *)
(*         {| *)
(*           gs_flags        := flags; *)
(*           gs_regs         := regs; *)
(*           gs_callstack    := xstack0; *)
(*           gs_context_u128 := context_u128; *)

(*           gs_mem_pages    := mem_pages; *)
(*           gs_contracts    := contracts; *)
(*         |} *)
(*         {| *)
(*           gs_flags        := mk_fs Set_OF_LT Clear_EQ Clear_GT; *)
(*           gs_regs         := new_regs; *)
(*           gs_callstack    := pc_set exception_handler new_caller_stack; *)
(*           gs_context_u128 := zero128; *)


(*           gs_mem_pages    := mem_pages; *)
(*           gs_contracts    := contracts; *)
(*         |} *)



.

Inductive step: global_state -> global_state -> Prop :=
   | step_correct:
    forall flags contracts mem_pages xstack0 xstack1 ins context_u128 regs cond ergs_left new_gs, let gs0 := {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;
        |} in
let gs1 := {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := ergs_set ergs_left xstack1;
          gs_context_u128 := context_u128;
        |} in
      cond_activated cond flags ->

      check_requires_kernel ins (is_kernel xstack0) = true ->
      check_allowed_static_ctx ins (topmost_extframe xstack0).(ecf_is_static) = true ->
      fetch_instr regs xstack0 mem_pages (Ins ins cond) ->

      update_pc_regular xstack0 xstack1 ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left, false) ->
      step_ins ins gs1 new_gs ->
      step gs0 new_gs.

End Execution.
