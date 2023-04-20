Require Common Memory Instruction State. 

Import ZArith Common MemoryBase Memory Instruction State ZMod.


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
  Inductive sp_adjustment : global_state -> reg_name -> u16 -> stack_address -> Prop :=
  | spa_stack_pp: forall gs reg offset_reg offset_imm offset_reg_clipped
                     stackaddr_delta
                     overflow_ignored,
      fetch_gpr (gs_regs gs) reg (IntValue offset_reg) ->
      offset_reg_clipped = ZMod.resize word_bits _ offset_reg ->

      uadd_overflow _ offset_reg_clipped offset_imm = (stackaddr_delta, overflow_ignored) ->
      sp_adjustment gs reg offset_imm stackaddr_delta
.
kajsndkjasndajnsd

  (* IMPORTANT sort out offsets from effects *)
  Inductive sp_adjustment_from_arg: global_state -> arg_any -> stack_address -> Prop :=
  | spafg_stack_pp: forall gs reg offset_imm new_sp,
      sp_adjustment gs reg offset_imm new_sp ->
      sp_adjustment_from_arg gs (ArgStackPushPop reg offset_imm) new_sp
  | spafg_stack_pp: forall gs sp,
      forall reg,
      sp_adjustment_from_arg gs (ArgReg reg ) sp
.

  Inductive resolve_loc: global_state -> arg_any -> loc ->  Prop :=
  | rslv_reg: forall gs reg, resolve_loc gs (ArgReg reg) (LocReg reg)

  | rslv_stack_pp: forall gs reg base offset_imm sp_delta of_ignored new_sp,
      fetch_sp (gs_regs gs) base ->
      sp_adjustment gs reg offset_imm sp_delta ->

      uadd_overflow _ base sp_delta = (new_sp, of_ignored) ->
      resolve_loc gs (ArgStackPushPop reg offset_imm)
        (LocStackAddress new_sp)

  | rslv_stack_rel: forall gs reg base offset_imm sp_delta of_ignored new_sp,
      fetch_sp (gs_regs gs) base ->
      sp_adjustment gs reg offset_imm sp_delta ->

      uadd_overflow _ base sp_delta = (new_sp, of_ignored) ->
      resolve_loc gs (ArgStackOffset reg offset_imm)
        (LocStackAddress new_sp)

  | rslv_stack_abs: forall gs reg base abs_imm stackpage_id,
      active_stackpage_id gs stackpage_id ->
      fetch_sp (gs_regs gs) base ->

      resolve_loc gs (ArgStackAddr reg abs_imm)
        (LocStackAddress abs_imm)

  | rslv_code: forall gs reg code_id abs_imm addr,
      active_codepage_id gs code_id ->
     relative_code_addressing gs reg abs_imm addr ->
     resolve_loc gs (ArgCodeAddr reg abs_imm) (LocCodeAddr addr)
  .

  Inductive fetch_result :=
    | FetchIns (ins :instruction)
    | FetchPV (pv: primitive_value) .

  Inductive fetch_loc: global_state -> loc -> fetch_result -> Prop :=
  | fetch_reg:
    forall gs reg_name value,
      fetch_gpr (gs_regs gs) reg_name value ->
      fetch_loc gs (LocReg reg_name) (FetchPV value)
  | fetch_stackaddr:
    forall gs stackpage addr value,
      active_stackpage gs (StackPage _ _ stackpage) ->
      load_result _ addr stackpage value ->
      fetch_loc gs (LocStackAddress addr) (FetchPV value)
  | fetch_codeaddr:
    forall gs codepage addr ins,
      active_codepage gs (CodePage _ _ codepage) ->
      load_result _ addr codepage ins ->
      fetch_loc gs (LocCodeAddr addr) (FetchIns ins)
  | fetch_constaddr:
    forall gs constpage addr value,
      active_constpage gs (ConstPage _ _ constpage) ->
      load_result _ addr constpage value ->
      fetch_loc gs (LocConstAddr addr) (FetchPV (IntValue value))
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
      update_pc_regular (Build_regs_state gprs sp pc)
        (Build_regs_state gprs sp pc').

From RecordUpdate Require Import RecordSet.
#[export] Instance etaX : Settable _ := settable! Build_global_state <gs_flags
                                        ; gs_regs; gs_contracts ; gs_mem_pages; gs_callstack; gs_context_u128>.

Import RecordSetNotations.
Inductive step : global_state -> global_state -> Prop :=
 
  | step_NOOP:
    forall OF EQ GT regs regs' contracts mem_pages callstack context_u128 in1 in2 out1 out2
    exec_cond,
      let gs := {|
          gs_flags := mk_fs OF EQ GT;
          gs_regs := regs;
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
      update_pc_regular regs regs' ->
      update_sp_regular regs regs' ->

      sp_adjustment gs reg offset_imm stackaddr_delta

      
      step gs (gs <| gs_regs := regs'' |>).




 
        (* {| *)
        (*   gs_flags := mk_fs OF EQ GT; *)
        (*   gs_regs := regs'; *)
        (*   gs_mem_pages := mem_pages; *)
        (*   gs_contracts := contracts; *)
        (*   gs_callstack := callstack; *)
        (*   gs_context_u128 := context_u128; *)
        (* |}. *)
(* todo: adjust SP *)
