From RecordUpdate Require Import RecordSet.
Require Common Memory Instruction State.

Import ZArith Common MemoryBase Memory Instruction State ZMod.

(* Experimental: lens-like notations to set individual fields of records. *)
Import RecordSetNotations.
#[export] Instance etaX : Settable _ :=
  settable! Build_global_state <gs_flags
  ; gs_regs; gs_contracts ; gs_mem_pages; gs_callstack; gs_context_u128>.


(** TODO contract that manages code *)
Definition code_managing_contract_address : contract_address
  := ZMod.mk_int_mod_truncated 160 32770%Z.

(* TODO *)
Definition ergs_counter_type := u32.

(* TODO *)
Definition shard_id_type := u8.


(** * Execution *)

Section Execution.
  Definition ifEQ (fs: flags_state) : Prop :=
    match fs with
    | mk_fs OF_LT true GT => True
    | _ => False
    end.


  Inductive flags_activated:  exec_conditions_type -> flags_state -> Prop
    :=
  | ac_Always: forall fs,
      flags_activated IfAlways fs

  | ac_GT: forall fs,
      GT fs = true ->
      flags_activated IfGT fs

  | ac_EQ: forall fs,
      EQ fs = true -> flags_activated IfEQ fs

  | ac_LT: forall fs,
      OF_LT fs = true ->
      flags_activated IfLT fs

  | ac_GE1: forall fs,
      EQ fs = true ->
      flags_activated IfGE fs

  | ac_GE2: forall fs,
      GT fs = true ->
      flags_activated IfGE fs

  | ac_LE1: forall fs,
      OF_LT fs = true ->
      flags_activated IfLE fs
  | ac_LE2: forall fs,
      EQ fs = true ->
      flags_activated IfLE fs


  | ac_NotEQ: forall fs,
      EQ fs = false ->
      flags_activated IfNotEQ fs

  | ac_IfGTOrLT1: forall fs,
      GT fs = true ->
      flags_activated IfGTOrLT fs

  | ac_IfGTOrLT2: forall fs,
      OF_LT fs = true ->
      flags_activated IfGTOrLT fs
  .



  (** Location from where a value can be fetched. *)
  Inductive loc : Set :=
  | LocImm: u16 ->  loc
  | LocReg : reg_name ->  loc
  | LocStackAddress: stack_address -> loc
  | LocCodeAddr: code_address -> loc
  | LocConstAddr: const_address ->  loc
  | LocHeapAddr: mem_page_id -> mem_address -> loc
  | LocAuxHeapAddr: mem_page_id -> mem_address ->  loc.

  (** Fetching value from general purpose register. *)
  Inductive fetch_gpr : regs_state -> reg_name -> primitive_value -> Prop :=
  | fr_fetch:
    forall rs n regname val,
      reg_n n regname ->
      List.nth_error (rs_gprs rs) n = Some val ->
      fetch_gpr rs regname val.

  (** Fetching value of the stack pointer itself. *)
  Inductive fetch_sp : regs_state -> stack_address -> Prop :=
  | fsp_fetch:
    forall rs (sp_value:stack_address),
      rs_sp rs = sp_value ->
      fetch_sp rs sp_value
  .
  (** Fetching value of the program counter itself. *)
  Inductive fetch_pc : regs_state -> code_address -> Prop :=
  | fpc_fetch:
    forall rs (pc_value: code_address) ,
      rs_pc rs = pc_value ->
      fetch_pc rs pc_value
  .


  Inductive relative_code_addressing: global_state -> reg_name -> u16 -> code_address -> Prop :=
  | rca_code_pp: forall gs reg reg_val reg_val_clipped imm offset_reg_clipped
                   code_absolute overflow_ignored,
      fetch_gpr (gs_regs gs) reg (IntValue reg_val) ->
      reg_val_clipped = ZMod.resize word_bits code_address_bits reg_val ->
      uadd_overflow code_address_bits offset_reg_clipped imm = (code_absolute, overflow_ignored) ->
      relative_code_addressing gs reg imm code_absolute
  .

  (** delta = reg + imm *)
  Inductive sp_delta: regs_state -> reg_name -> u16 -> stack_address -> Prop :=
  | spa_stack_pp: forall regs reg offset_reg offset_imm offset_reg_clipped
                    stackaddr_delta
                    overflow_ignored,
      fetch_gpr regs reg (IntValue offset_reg) ->
      offset_reg_clipped = ZMod.resize word_bits _ offset_reg ->

      uadd_overflow _ offset_reg_clipped offset_imm = (stackaddr_delta, overflow_ignored) ->
      sp_delta regs reg offset_imm stackaddr_delta
  .

  Inductive resolve_loc: global_state -> arg_any -> loc ->  Prop :=
  | rslv_reg: forall gs reg, resolve_loc gs (ArgReg reg) (LocReg reg)

  | rslv_imm: forall gs imm, resolve_loc gs (ArgImm imm) (LocImm imm)

  | rslv_stack_pp: forall gs reg base offset_imm dlt_sp of_ignored new_sp,
      fetch_sp (gs_regs gs) base ->
      sp_delta gs.(gs_regs) reg offset_imm dlt_sp ->

      uadd_overflow _ base dlt_sp = (new_sp, of_ignored) ->
      resolve_loc gs (ArgStackPushPop reg offset_imm)
        (LocStackAddress new_sp)

  | rslv_stack_rel: forall gs reg base offset_imm dlt_sp of_ignored new_sp,
      fetch_sp gs.(gs_regs) base ->
      sp_delta gs.(gs_regs) reg offset_imm dlt_sp ->

      uadd_overflow _ base dlt_sp = (new_sp, of_ignored) ->
      resolve_loc gs (ArgStackOffset reg offset_imm)
        (LocStackAddress new_sp)

  | rslv_stack_abs: forall gs reg base abs_imm stackpage_id,
      active_stackpage_id gs.(gs_callstack) stackpage_id ->
      fetch_sp gs.(gs_regs) base ->

      resolve_loc gs (ArgStackAddr reg abs_imm)
        (LocStackAddress abs_imm)

  | rslv_code: forall gs reg code_id abs_imm addr,
      active_codepage_id gs.(gs_callstack) code_id ->
      relative_code_addressing gs reg abs_imm addr ->
      resolve_loc gs (ArgCodeAddr reg abs_imm) (LocCodeAddr addr)
  .

  Inductive fetch_result : Set :=
  | FetchIns (ins :instruction)
  | FetchPV (pv: primitive_value) .

  (* Address resolution *)
  Inductive fetch_loc: global_state -> loc -> fetch_result -> Prop :=
  | fetch_reg:
    forall gs reg_name value,
      fetch_gpr (gs_regs gs) reg_name value ->
      fetch_loc gs (LocReg reg_name) (FetchPV value)

  | fetch_imm:
    forall gs imm imm',
      imm' = mk_int_mod_truncated word_bits (int_val _ imm) ->
      fetch_loc gs (LocImm imm) (FetchPV (IntValue imm'))

  | fetch_stackaddr:
    forall gs stackpage addr value,
      active_stackpage gs.(gs_mem_pages) gs.(gs_callstack) (StackPage _ _ stackpage) ->
      load_result _ addr stackpage value ->
      fetch_loc gs (LocStackAddress addr) (FetchPV value)
  | fetch_codeaddr:
    forall gs codepage addr ins,
      active_codepage gs.(gs_mem_pages) gs.(gs_callstack) (CodePage _ _ codepage) ->
      load_result _ addr codepage ins ->
      fetch_loc gs (LocCodeAddr addr) (FetchIns ins)
  | fetch_constaddr:
    forall gs constpage addr value,
      active_constpage gs.(gs_mem_pages) gs.(gs_callstack) (ConstPage _ _ constpage) ->
      load_result _ addr constpage value ->
      fetch_loc gs (LocConstAddr addr) (FetchPV (IntValue value))
  (* TODO Come back for UMA; reading byte sequences is already implemented, see
  tests in MemoryBase.v *)
  (* | fetch_heapaddr: *)
  (*   forall gs page addr value, *)
  (*     active_heappage gs (DataPage _ _ page) -> *)
  (*     (* here we need to glue together 256 bits from 32 bytes *) *)
  (*     load_result _ addr const_page value -> *)
  (*     fetch_loc gs (LocConstAddr addr) (FetchPV (IntValue value)) *)

  (* | fetch_auxheapaddr: *)
  .


  (* To encode an instruction:
- addressing mode effect on sp
- PC
- exceptions
   *)
  Inductive fetch_instr : global_state -> instruction -> Prop :=
  | fi_fetch: forall gs pc ins,
      fetch_pc (gs_regs gs) pc ->
      fetch_loc gs (LocCodeAddr pc) (FetchIns ins) ->
      fetch_instr gs ins.

  Inductive update_pc_regular : regs_state -> regs_state -> Prop :=
  | fp_update:
    forall pc sp gprs pc',
      (pc',false) = uinc_overflow _ pc ->
      update_pc_regular (mk_regs gprs sp pc) (mk_regs gprs sp pc').

  (* may affect SP through addressing on in1 and out1.
     Takes effect before SP is read by the bytecode. sort out offsets from effects *)
  Inductive sp_addressing_delta: regs_state -> arg_any -> stack_address -> Prop :=
  | spafg_stack_pp: forall regs reg offset_imm new_sp,
      sp_delta regs reg offset_imm new_sp ->
      sp_addressing_delta regs (ArgStackPushPop reg offset_imm) new_sp
  | spafg_stack_reg_none: forall regs arg,
      (forall reg offset_imm, arg <> ArgStackPushPop reg offset_imm) ->
      sp_addressing_delta regs arg stack_address_zero.

  (* partial because has to be applied twice: for in1 and for out1 arguments.  *)
  Inductive update_sp_addressing_partial: arg_any -> regs_state -> regs_state -> Prop :=
  | usap_update_partial:
    forall gprs pc sp delta_sp sp' arg ,
      sp_addressing_delta (mk_regs gprs sp pc) arg delta_sp ->
      (sp',false) = uadd_overflow _ sp delta_sp ->
      update_sp_addressing_partial arg (mk_regs gprs sp pc) (mk_regs gprs sp' pc).

  Inductive update_sp_addressing_full: arg_any -> arg_any -> regs_state -> regs_state -> Prop :=
  | usap_update_full: forall arg1 arg2 regs0 regs1 regs2,
    update_sp_addressing_partial arg1 regs0 regs1 ->
    update_sp_addressing_partial arg2 regs1 regs2 ->
    update_sp_addressing_full arg1 arg2 regs0 regs2.



  Inductive step : global_state -> global_state -> Prop :=
  | step_NOOP:
    forall flags contracts mem_pages callstack context_u128 in1 in2
      out1 out2 regs0 regs1 regs2
      exec_cond,
      let gs := {|
                 gs_flags := flags;
                 gs_regs := regs0;
                 gs_mem_pages := mem_pages;
                 gs_contracts := contracts;
                 gs_callstack := callstack;
                 gs_context_u128 := context_u128;
               |} in

      fetch_instr gs {|
                    ins_spec := OpNoOp in1 in2 out1 out2;
                    ins_mods := ModEmpty;
                    ins_cond := exec_cond
                  |} ->
      flags_activated exec_cond flags ->
      update_pc_regular regs0 regs1 ->
      update_sp_addressing_full in1 out1 regs1 regs2 ->

      step gs (gs <| gs_regs := regs2 |>).
(* TODO think about other modifiers *)

  
  (* | step_ADD: *)
  (*   forall OF_LT EQ GT contracts mem_pages callstack context_u128 in1 in2 *)
  (*     out1 out2 regs0 regs1 regs2 *)
  (*     loc1 loc2 arg1 arg2 new_OF new_EQ res *)
  (*     exec_cond, *)
  (*     let gs := {| *)
  (*                gs_flags := mk_fs OF_LT EQ GT; *)
  (*                gs_regs := regs0; *)
  (*                gs_mem_pages := mem_pages; *)
  (*                gs_contracts := contracts; *)
  (*                gs_callstack := callstack; *)
  (*                gs_context_u128 := context_u128; *)
  (*              |} in *)
  (*     fetch_instr gs {| *)
  (*                   ins_spec := OpAdd in1 in2 out1 ; *)
  (*                   ins_mods := ModEmpty; *)
  (*                   ins_cond := exec_cond *)
  (*                 |} -> *)
  (*     resolve_loc gs in1 loc1 -> *)
  (*     resolve_loc gs in2 loc2 -> *)
  (*     fetch_loc gs loc1 (FetchPV (IntValue arg1)) -> *)
  (*     fetch_loc gs loc2 (FetchPV (IntValue arg2)) -> *)
  (*     uadd_overflow _ arg1 arg2 = (res, new_OF) -> *)
  (*     new_EQ = if Z.eq_dec (int_val _ res) 0%Z then true else false -> *)

  (*                                                             (*TODO set GT, *)
  (*     implement SET_FLAGS *) *)
  (*     flags_activated exec_cond (mk_fs -> *)
  (*     update_pc_regular regs0 regs1 -> *)
  (*     update_sp_addressing_full in1 out1 regs1 regs2 -> *)
  (*     step gs (gs <| gs_regs := regs2 |> <| gs_flags := mk_fs new_OF new_EQ|>). *)
End Execution.
