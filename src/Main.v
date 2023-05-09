From RecordUpdate Require Import RecordSet.
Require Common Memory Instruction State Addressing.

Import ZArith Addressing Common MemoryBase Memory Instruction State ZMod.

(* Experimental: lens-like notations to set individual fields of records. *)
Import RecordSetNotations.
#[export] Instance etaXGS : Settable _ :=
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
      fetch_pc (gs_callstack gs) pc ->
      fetch_loc gs (LocCodeAddr pc) (FetchIns ins) ->
      fetch_instr gs ins.

  Inductive fetch_op: global_state -> opcode_specific -> common_mod -> cond -> Prop :=
  | fo_fetch: forall gs op mods cond,
      fetch_instr gs (Ins op mods cond) ->
      fetch_op gs op mods cond.

  Inductive update_pc_regular : execution_frame -> execution_frame -> Prop :=
  | fp_update:
    forall pc pc' ef ef',
      fetch_pc ef pc ->
      (pc',false) = uinc_overflow _ pc ->
      update_pc pc ef ef' ->
      update_pc_regular ef ef'.

  (* TODO needs to accept  a list of flags to reset or to keep? *)
  Inductive mod_set_flags: mod_clear_flags -> flags_state -> flags_state -> Prop :=
    | msf_set:
      forall fs, mod_set_flags ClearFlags fs (mk_fs Clear_OF_LT Clear_EQ Clear_GT)
    | msf_clr:
      forall fs, mod_set_flags NoClearFlags fs fs.


  Inductive step : global_state -> global_state -> Prop :=
  | step_NOOP:
    forall flags flags' mod_swap mod_sf contracts mem_pages xstack0 xstack1 xstack' context_u128 in1 in2
      out1 out2 regs cond,
      let gs := {|
                 gs_flags := flags;
                 gs_regs := regs;
                 gs_mem_pages := mem_pages;
                 gs_contracts := contracts;
                 gs_callstack := xstack0;
                 gs_context_u128 := context_u128;
               |} in

      fetch_instr gs {|
                    ins_spec := OpNoOp in1 in2 out1 out2;
                    ins_mods := mk_cmod mod_swap mod_sf;
                    ins_cond := cond
                  |} ->
      cond_activated cond flags ->
      mod_set_flags mod_sf flags flags' ->
      update_pc_regular xstack0 xstack1 ->
      resolve_effect in1 out1 xstack1 xstack' ->

      step gs
           {|
             gs_flags := flags';
             gs_regs := regs;
             gs_mem_pages := mem_pages;
             gs_contracts := contracts;
             gs_callstack := xstack';
             gs_context_u128 := context_u128;
           |}
.
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
  (*     cond_activated exec_cond (mk_fs -> *)
  (*     update_pc_regular regs0 regs1 -> *)
  (*     update_sp_addressing_full in1 out1 regs1 regs2 -> *)
  (*     step gs (gs <| gs_regs := regs2 |> <| gs_flags := mk_fs new_OF new_EQ|>). *)
End Execution.
