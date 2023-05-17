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
    op1 op2 op1' op2' swap set_flags out_loc result flags_candidate flags0 flags',
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
    flags' = apply_set_flags set_flags flags0 flags_candidate ->
    binop_effect ef0 regs mm flags0 in1 in2 out swap set_flags f (ef', regs', mm', flags').


Definition usub_saturate {bits} (x y: int_mod bits) :=
  let (res, underflow) := x - y in
  if underflow then int_mod_of bits 0%Z else res.

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
  forall flags contracts mem_pages xstack0 xstack1 xstack' context_u128 in1 out1 regs,
    resolve_effect__in in1 xstack0 xstack1 ->
    resolve_effect__out out1 xstack1 xstack' ->
    step_ins (OpModSP in1 out1)
             {|
               gs_flags        := flags;
               gs_regs         := regs;
               gs_mem_pages    := mem_pages;
               gs_contracts    := contracts;
               gs_callstack    := xstack0;
               gs_context_u128 := context_u128;
             |}
             {|
               gs_flags        := flags;
               gs_regs         := regs;
               gs_mem_pages    := mem_pages;
               gs_contracts    := contracts;
               gs_callstack    := xstack';
               gs_context_u128 := context_u128;
             |}
(**
<<
## Add
Unsigned addition of two numbers.
>>
*)
  | step_Add:
    forall flags flags' mod_swap mod_sf contracts mem_pages mem_pages' xstack xstack' context_u128 (in1:in_any) (in2:in_reg) out regs regs',
      
      binop_effect xstack regs mem_pages flags in1 in2 out mod_swap mod_sf
        (fun x y =>
           let (result, OF') := x + y in
           let EQ' := EQ_of_bool (result == zero256) in
           let GT' := GT_of_bool (negb EQ' && negb OF') in
           (result, mk_fs (OF_LT_of_bool OF') EQ' GT'))
        (xstack', regs', mem_pages', flags') ->

      step_ins (OpAdd in1 in2 out mod_swap mod_sf)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags';
          gs_regs := regs';
          gs_mem_pages := mem_pages';
          gs_contracts := contracts;
          gs_callstack := xstack';
          gs_context_u128 := context_u128;
        |}
(**
<<
## Sub
Unsigned subtraction of two numbers.
>>
*)

| step_Sub:
    forall flags flags' mod_swap mod_sf contracts mem_pages mem_pages' xstack xstack' context_u128 (in1:in_any) (in2:in_reg) out regs regs',

      binop_effect xstack regs mem_pages flags in1 in2 out mod_swap mod_sf
        (fun x y =>
           let (result, OF') := x - y in
           let EQ' := EQ_of_bool (result == zero256) in
           let GT' := GT_of_bool (negb EQ' && negb OF') in
           (result, mk_fs (OF_LT_of_bool OF') EQ' GT'))
        (xstack', regs', mem_pages', flags') ->

      step_ins (OpSub in1 in2 out mod_swap mod_sf)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags';
          gs_regs := regs';
          gs_mem_pages := mem_pages';
          gs_contracts := contracts;
          gs_callstack := xstack';
          gs_context_u128 := context_u128;
        |}
(**
<<
## And
Bitwise AND of two numbers.
>>
*)

| step_And:
    forall flags flags' mod_swap mod_sf contracts mem_pages mem_pages' xstack xstack' context_u128 (in1:in_any) (in2:in_reg) out regs regs',

      binop_effect xstack regs mem_pages flags in1 in2 out mod_swap mod_sf
        (fun x y => let result := bitwise_and _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
        (xstack', regs', mem_pages', flags') ->

      step_ins (OpAnd in1 in2 out mod_swap mod_sf)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags';
          gs_regs := regs';
          gs_mem_pages := mem_pages';
          gs_contracts := contracts;
          gs_callstack := xstack';
          gs_context_u128 := context_u128;
        |}
(**
<<
## Or
Bitwise OR of two numbers.
>>
*)
| step_Or:
    forall flags flags' mod_swap mod_sf contracts mem_pages mem_pages' xstack xstack' context_u128 (in1:in_any) (in2:in_reg) out regs regs',

      binop_effect xstack regs mem_pages flags in1 in2 out mod_swap mod_sf
        (fun x y => let result := bitwise_or _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
        (xstack', regs', mem_pages', flags') ->

      step_ins (OpOr in1 in2 out mod_swap mod_sf)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags';
          gs_regs := regs';
          gs_mem_pages := mem_pages';
          gs_contracts := contracts;
          gs_callstack := xstack';
          gs_context_u128 := context_u128;
        |}
        
(**
<<
## Xor
Bitwise XOR of two numbers.
>>
*)
| step_Xor:
    forall flags flags' mod_swap mod_sf contracts mem_pages mem_pages' xstack xstack' context_u128 (in1:in_any) (in2:in_reg) out regs regs',

      binop_effect xstack regs mem_pages flags in1 in2 out mod_swap mod_sf
        (fun x y => let result := bitwise_or _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
        (xstack', regs', mem_pages', flags') ->

      step_ins (OpXor in1 in2 out mod_swap mod_sf)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags';
          gs_regs := regs';
          gs_mem_pages := mem_pages';
          gs_contracts := contracts;
          gs_callstack := xstack';
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
          gs_flags := flags;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags_clear;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := InternalCall new_frame (ergs_set ergs_left xstack0);
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
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags_clear;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := InternalCall new_frame (ergs_zero xstack0);
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
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags_clear;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := InternalCall new_frame (ergs_zero xstack1);
          gs_context_u128 := context_u128;
        |}

 (**
<<
## Return (normal return, not panic/revert)

>>
  *)
| step_RetLocal_nolabel:
    forall flags contracts mem_pages cf caller_stack caller_stack' context_u128 regs _ignored,

      let xstack := InternalCall cf caller_stack in

      ergs_reimburse (ergs_remaining xstack) caller_stack caller_stack' ->
      step_ins (OpRet _ignored None)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := flags_clear;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := caller_stack';
          gs_context_u128 := context_u128;
        |}

| step_RetLocal_label:
  forall gs gs' _ignored label,
    step_ins (OpRet _ignored None) gs gs' ->
    step_ins (OpRet _ignored (Some label)) gs (gs' <| gs_callstack ::= pc_set label |>)

(**
<<
## Revert (not return/panic)

>>
  *)


| step_RevertLocal_nolabel:
  forall gs gs' _ignored,
    step_ins (OpRet _ignored None) gs gs' ->
    let dest := active_exception_handler gs.(gs_callstack) in
    step_ins (OpRevert _ignored None) gs (gs' <| gs_callstack ::= pc_set dest |>)

| step_RevertLocal_label:
  forall gs gs' _ignored label,
    step_ins (OpRet _ignored (Some label)) gs gs' ->
    step_ins (OpRevert _ignored (Some label)) gs gs'

(**
<<
## Panic (not return/revert)

>>
  *)
| step_PanicLocal_nolabel:
  forall gs gs' _ignored,
    step_ins (OpRevert _ignored None) gs gs' ->

    step_ins (OpPanic None) gs (gs' <| gs_flags ::= set_overflow |>)
| step_PanicLocal_label:
  forall gs gs' label,
    step_ins (OpPanic None) gs gs' ->

    step_ins (OpPanic (Some label)) gs (gs' <| gs_callstack ::= pc_set label |>).



(*

| step_RetExt_UseHeap:
    forall flags contracts mem_pages cf caller_stack caller_stack' context_u128 regs label_ignored (arg:in_reg) in_ptr_encoded in_ptr in_ptr_shrunk paid_growth bytes_grown heap_page_id,

      let xstack0 := ExternalCall cf (Some caller_stack) in
      (* Panic if not a pointer*)
      resolve_fetch_value regs xstack0 mem_pages arg (PtrValue in_ptr_encoded) ->

      Ret.ABI.(decode) in_ptr_encoded = Ret.mk_params in_ptr UseHeap ->

      (* Panic if either of two does not hold *)
      page_older in_ptr.(fp_mem_page) cf.(ecf_mem_context)  = false ->
      validate in_ptr true = no_exceptions ->

      fat_ptr_shrink in_ptr in_ptr_shrunk ->

      growth_bytes in_ptr cf.(ecf_mem_context).(ctx_heap_bound) bytes_grown ->

      ergs_remaining xstack0 - Ergs.growth_cost bytes_grown = (paid_growth, false) ->

      ergs_reimburse paid_growth caller_stack caller_stack' ->
      active_heappage_id xstack0 heap_page_id ->

      let out_ptr := in_ptr_shrunk <| fp_mem_page := heap_page_id |> in
      let out_ptr_enc := FatPointer.ABI.(encode) out_ptr in

      step_ins (OpRet arg label_ignored)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := flags_clear;
          gs_regs         := regs_state_zero
                               <| gprs_r1 := PtrValue out_ptr_enc |>
                               <| gprs_r2 := reg_reserved |>
                               <| gprs_r3 := reg_reserved |>
                               <| gprs_r4 := reg_reserved |>;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := caller_stack';
          gs_context_u128 := zero128;
        |}

.

Inductive step: global_state -> global_state -> Prop :=
   | step_correct:
    forall flags contracts mem_pages xstack0 xstack1 ins context_u128 regs cond ergs_left gs',
let gs0 := {|
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
      fetch_instr regs xstack0 mem_pages (Ins ins cond) ->

      update_pc_regular xstack0 xstack1 ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left, false) ->
      step_ins ins gs1 gs' ->
      step gs0 gs'
.*)
End Execution.
