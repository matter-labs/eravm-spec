Require Common Memory Instruction State.

Import ZArith ZMod Common MemoryBase Memory Instruction State Arg List ListNotations.

(** Location from where a value can be fetched. *)
Inductive loc : Set :=
| LocImm: u16 ->  loc
| LocReg : reg_name ->  loc
| LocStackAddress: stack_address -> loc
| LocCodeAddr: code_address -> loc
| LocConstAddr: const_address ->  loc
| LocHeapAddr: mem_page_id -> mem_address -> loc
| LocAuxHeapAddr: mem_page_id -> mem_address ->  loc.


Section GPR.
(** Fetching value from general purpose register. *)

  Definition fetch_gpr (rs:regs_state) (r:reg_name) : primitive_value :=
    match r with
    | R0 => IntValue zero256
    | R1 => gprs_r1 rs
    | R2 => gprs_r2 rs
    | R3 => gprs_r3 rs
    | R4 => gprs_r4 rs
    | R5 => gprs_r5 rs
    | R6 => gprs_r6 rs
    | R7 => gprs_r7 rs
    | R8 => gprs_r8 rs
    | R9 => gprs_r9 rs
    | R10 => gprs_r10 rs
    | R11 => gprs_r11 rs
    | R12 => gprs_r12 rs
    | R13 => gprs_r13 rs
    | R14 => gprs_r14 rs
    | R15 => gprs_r15 rs
    end.

(** Storing value to general purpose registers. *)



(** Storing value to general purpose registers. *)
Inductive store_gpr : regs_state -> reg_name -> primitive_value -> regs_state -> Prop :=
| fr_store1 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
  store_gpr
    (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R1 pv
    (mk_regs pv r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
| fr_store2 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
  store_gpr
    (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R2 pv
    (mk_regs r1 pv r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
| fr_store3 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
  store_gpr
    (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R3 pv
    (mk_regs r1 r2 pv r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
| fr_store4 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
  store_gpr
    (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R4 pv
    (mk_regs r1 r2 r3 pv r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
| fr_store5 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
  store_gpr
    (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R5 pv
    (mk_regs r1 r2 r3 r4 pv r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
| fr_store6 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
    store_gpr
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R6 pv
      (mk_regs r1 r2 r3 r4 r5 pv r7 r8 r9 r10 r11 r12 r13 r14 r15)
| fr_store7 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
    store_gpr
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R7 pv
      (mk_regs r1 r2 r3 r4 r5 r6 pv r8 r9 r10 r11 r12 r13 r14 r15)
| fr_store8 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
    store_gpr
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R8 pv
      (mk_regs r1 r2 r3 r4 r5 r6 r7 pv r9 r10 r11 r12 r13 r14 r15)
| fr_store9 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
    store_gpr
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R9 pv
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 pv r10 r11 r12 r13 r14 r15)
| fr_store10 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
    store_gpr
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R10 pv
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 pv r11 r12 r13 r14 r15)
| fr_store11 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
    store_gpr
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R11 pv
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 pv r12 r13 r14 r15)
| fr_store12 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
    store_gpr
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R12 pv
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 pv r13 r14 r15)
| fr_store13 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
    store_gpr
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R13 pv
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 pv r14 r15)
| fr_store14 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
    store_gpr
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R14 pv
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 pv r15)
| fr_store15 :
  forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
    store_gpr
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R15 pv
      (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 pv)
.

End GPR.


Section AddressResolution.
Inductive reg_rel_addressing addr_bits : regs_state -> reg_name -> int_mod addr_bits -> int_mod addr_bits -> Prop :=
| rca_code_pp: forall regs reg reg_val base ofs
                 abs OF_ignored,
    fetch_gpr regs reg = IntValue reg_val ->
    extract_address addr_bits reg_val base ->
    uadd_overflow _ base ofs = (abs, OF_ignored) ->
    reg_rel_addressing addr_bits regs reg ofs abs.

Definition reg_rel_code_addressing
  : regs_state -> reg_name -> u16 -> code_address -> Prop
  := reg_rel_addressing code_address_bits.

Definition reg_rel_const_addressing
  : regs_state -> reg_name -> u16 -> const_address -> Prop
  := reg_rel_addressing const_address_bits.

Definition reg_rel_stack_addressing
  : regs_state -> reg_name -> u16 -> stack_address -> Prop
  := reg_rel_addressing stack_page_params.(address_bits).

(** delta = reg + imm *)
Definition sp_delta_abs: regs_state -> reg_name -> u16 -> stack_address -> Prop := reg_rel_stack_addressing.


Inductive loc_reg: reg_io -> loc ->  Prop :=
| rslv_reg_aux: forall reg, loc_reg (Reg reg) (LocReg reg).

Inductive loc_imm: imm_in -> loc ->  Prop :=
|rslv_imm_aux : forall imm, loc_imm (Imm imm) (LocImm imm).

Inductive loc_code: regs_state -> code_in -> loc -> Prop :=
| rslv_code_aux: forall regs reg abs_imm addr,
    reg_rel_code_addressing regs reg abs_imm addr ->
    loc_code regs (CodeAddr reg abs_imm) (LocCodeAddr addr).

Inductive loc_const: regs_state -> const_in -> loc -> Prop :=
| rslv_const_aux: forall regs reg abs_imm addr,
    reg_rel_const_addressing regs reg abs_imm addr ->
    loc_const regs (ConstAddr reg abs_imm) (LocConstAddr addr).

Inductive loc_stack_io: execution_frame -> regs_state -> stack_io -> loc -> Prop :=
| rslv_stack_rel_aux: forall ef regs reg base offset_imm dlt_sp sp_rel OF_ignore,
    fetch_sp ef base ->
    sp_delta_abs regs reg offset_imm dlt_sp ->
    (sp_rel, OF_ignore) = usub_overflow _ base dlt_sp->
    loc_stack_io ef regs (RelSP reg offset_imm) (LocStackAddress sp_rel)
| rslv_stack_abs_aux: forall ef regs reg imm abs,
    reg_rel_stack_addressing regs reg imm abs ->
    loc_stack_io ef regs (Absolute reg imm) (LocStackAddress imm).

Inductive loc_stack_in_only: execution_frame -> regs_state -> stack_in_only -> loc -> Prop :=
| rslv_stack_gpop_aux: forall ef regs reg sp ofs dlt_sp new_sp OF_ignore,
    fetch_sp ef sp ->
    sp_delta_abs regs reg ofs dlt_sp ->
    (new_sp, OF_ignore) = usub_overflow _ sp dlt_sp ->
    loc_stack_in_only ef regs (RelSpPop reg ofs) (LocStackAddress new_sp)
.

Inductive loc_stack_out_only: execution_frame -> regs_state -> stack_out_only -> loc -> Prop :=
| rslv_stack_gpush_aux: forall ef regs reg sp ofs dlt_sp new_sp OF_ignore,
    fetch_sp ef sp ->
    sp_delta_abs regs reg ofs dlt_sp ->
    (new_sp, OF_ignore) = uadd_overflow _ sp dlt_sp ->
    loc_stack_out_only ef regs (RelSpPush reg ofs) (LocStackAddress new_sp)
.

Inductive resolve: execution_frame -> regs_state -> any -> loc -> Prop :=
| rslv_reg : forall ef rs r loc,
    loc_reg r loc ->
    resolve ef rs (AnyReg r) loc
| rslv_imm: forall ef rs imm loc,
    loc_imm imm loc ->
    resolve ef rs (AnyImm imm) loc
| rslv_stack_io: forall ef regs arg loc,
    loc_stack_io ef regs arg loc ->
    resolve ef regs (AnyStack (StackAnyIO arg)) loc
| rslv_stack_in: forall ef regs arg loc,
    loc_stack_in_only ef regs arg loc ->
    resolve ef regs (AnyStack (StackAnyIn arg)) loc
| rslv_stack_out: forall ef regs arg loc,
    loc_stack_out_only ef regs arg loc ->
    resolve ef regs (AnyStack (StackAnyOut arg)) loc
| rslv_code: forall ef regs arg loc,
    loc_code regs arg loc ->
    resolve ef regs (AnyCode arg) loc
| rslv_const: forall ef regs arg loc,
    loc_const regs arg loc ->
    resolve ef regs (AnyConst arg) loc
.

Inductive resolve_effect__in: in_any -> execution_frame -> execution_frame -> Prop :=
| rslv_stack_in_effect: forall ef ef' regs sp' reg ofs arg,
    loc_stack_in_only ef regs  arg (LocStackAddress sp') ->
    update_sp sp' ef ef' ->
    resolve_effect__in  (InStack (StackInOnly (RelSpPop reg ofs)))  ef ef'
| rslv_stack_in_effect_none: forall ef arg,
    (forall reg ofs, arg <> InStack (StackInOnly (RelSpPop reg ofs))) ->
    resolve_effect__in  arg  ef ef.

Inductive resolve_effect__out: out_any -> execution_frame -> execution_frame -> Prop :=
| rslv_stack_out_effect: forall ef ef' regs sp' reg ofs arg,
    loc_stack_out_only ef regs  arg (LocStackAddress sp') ->
    update_sp sp' ef ef' ->
    resolve_effect__out  (OutStack (StackOutOnly (RelSpPush reg ofs)))  ef ef'
| rslv_stack_out_effect_none: forall ef arg,
    (forall reg ofs, arg <> OutStack (StackOutOnly (RelSpPush reg ofs))) ->
    resolve_effect__out  arg  ef ef.

Inductive resolve_effect: in_any -> out_any -> execution_frame -> execution_frame -> Prop :=
| rslv_effect_full: forall arg1 arg2 ef1 ef2 ef3,
    resolve_effect__in arg1 ef1 ef2 ->
    resolve_effect__out arg2 ef2 ef3 ->
    resolve_effect arg1 arg2 ef1 ef3.

End AddressResolution.

Section FetchStore.

Inductive fetch_result : Set :=
| FetchIns (ins :instruction)
| FetchPV (pv: primitive_value) .

(* Address resolution *)
Inductive fetch_loc: regs_state -> execution_frame -> mem_manager -> loc -> fetch_result -> Prop :=
| fetch_reg:
  forall regs ef mm reg_name value,
    fetch_gpr regs reg_name = value ->
    fetch_loc regs ef mm (LocReg reg_name) (FetchPV value)

| fetch_imm:
  forall regs ef mm imm imm',
    imm' = resize _ word_bits imm ->
    fetch_loc regs ef mm (LocImm imm) (FetchPV (IntValue imm'))

| fetch_stackaddr:
  forall regs ef mm stackpage addr value,
    active_stackpage mm ef (StackPage _ _ stackpage) ->
    load_result _ addr stackpage value ->
    fetch_loc regs ef mm (LocStackAddress addr) (FetchPV value)
| fetch_codeaddr:
  forall regs ef mm codepage addr ins,
    active_codepage mm ef (CodePage _ _ codepage) ->
    load_result _ addr codepage ins ->
    fetch_loc regs ef mm (LocCodeAddr addr) (FetchIns ins)
| fetch_constaddr:
  forall regs ef mm constpage addr value,
    active_constpage mm ef (ConstPage _ _ constpage) ->
    load_result _ addr constpage value ->
    fetch_loc regs ef mm (LocConstAddr addr) (FetchPV (IntValue value))

.
(* TODO UMA; reading byte sequences is already implemented, see
  tests in MemoryBase.v *)

Inductive fetch_instr : regs_state -> execution_frame -> mem_manager -> instruction -> Prop :=
| fi_fetch: forall regs ef mm pc ins,
    fetch_pc ef pc ->
    fetch_loc regs ef mm (LocCodeAddr pc) (FetchIns ins) ->
    fetch_instr regs ef mm ins.

Inductive fetch_op: regs_state -> execution_frame -> mem_manager -> opcode_specific -> common_mod -> cond -> Prop :=
| fo_fetch: forall regs ef mm op mods cond,
    fetch_instr regs ef mm (Ins op mods cond) ->
    fetch_op regs ef mm op mods cond.



Inductive store_loc: regs_state -> execution_frame -> mem_manager
                     -> primitive_value -> loc -> (regs_state * mem_manager ) -> Prop :=
| store_reg:
  forall regs regs' ef mm reg_name value,
    store_gpr regs reg_name value regs' ->
    store_loc regs ef mm value (LocReg reg_name) (regs', mm)

| store_stackaddr:
  forall regs ef mm mm' stackpage addr value pid stackpage',
    active_stackpage_id ef pid ->
    active_stackpage mm ef (StackPage _ _ stackpage) ->
    store_result _ addr stackpage value stackpage' ->
    mem_page_replace mm pid (StackPage _ _ stackpage') mm' ->
    store_loc regs ef mm value (LocStackAddress addr) (regs, mm')
.
(* TODO UMA related *)


Inductive resolve_fetch_word: regs_state -> execution_frame -> mem_manager -> Arg.any -> word_type -> Prop :=
| rf_resfetch: forall ef mm regs arg loc res,
    resolve ef regs arg loc ->
    fetch_loc regs ef mm loc (FetchPV (IntValue res)) ->
    resolve_fetch_word regs ef mm arg res.


Inductive resolve_store: regs_state -> execution_frame -> mem_manager
                         -> Arg.out_any -> primitive_value -> regs_state * mem_manager
                         -> Prop :=
  | rs_resstore: forall ef mm regs arg loc_out pv regs' mm',
      resolve ef regs (out_any_incl arg) loc_out ->
      store_loc regs ef mm pv loc_out (regs', mm') ->
      resolve_store regs ef mm arg pv (regs', mm').

End FetchStore.
