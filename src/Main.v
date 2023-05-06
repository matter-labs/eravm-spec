From RecordUpdate Require Import RecordSet.
Require Common Memory Instruction State Addressing.

Import ZArith Addressing Common MemoryBase Memory Instruction State ZMod.

(* Experimental: lens-like notations to set individual fields of records. *)
Import RecordSetNotations.
#[export] Instance etaX : Settable _ :=
  settable! Build_global_state <gs_flags
  ; gs_regs; gs_contracts ; gs_mem_pages; gs_callstack; gs_context_u128>.


(** TODO contract that manages code *)
Definition code_managing_contract_address : contract_address
  := ZMod.int_mod_of 160 32770%Z.

(* TODO *)
Definition ergs_counter_type := u32.

(* TODO *)
Definition shard_id_type := u8.


(** * Execution *)

Section Execution.
  Import Arg.

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
      imm' = resize _ word_bits imm ->
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

  .
  (* TODO UMA; reading byte sequences is already implemented, see
  tests in MemoryBase.v *)

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


  Inductive mod_set_flags: bool -> flags_state -> flags_state -> Prop :=
    | msf_set:
      forall fs, mod_set_flags true fs (mk_fs false false false)
    | msf_clr:
      forall fs, mod_set_flags false fs fs.

  Inductive step : global_state -> global_state -> Prop :=
  | step_NOOP:
    forall flags flags' mod_sf contracts mem_pages callstack context_u128 in1 in2
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
                    ins_mods := mk_cmod false mod_sf;
                    ins_cond := exec_cond
                  |} ->
      flags_activated exec_cond flags ->
      mod_set_flags mod_sf flags flags' ->
      update_pc_regular regs0 regs1 ->
      resolve_effect in1 out1 regs1 regs2 ->

      step gs (gs <| gs_flags := flags' |> <| gs_regs := regs2 |>).
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
