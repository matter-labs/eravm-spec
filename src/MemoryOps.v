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
Inductive fetch_gpr : regs_state -> reg_name -> primitive_value -> Prop :=
| fr_fetch:
  forall rs n regname val,
    reg_n n regname ->
    List.nth_error (rs_gprs rs) n = Some val ->
    fetch_gpr rs regname val.

(** Storing value to general purpose registers. *)
Inductive store_gpr : regs_state -> reg_name -> primitive_value -> regs_state -> Prop :=
| fr_store:
  forall rs n regname elem head tail val,
    reg_n n regname ->
    rs_gprs rs = head ++ elem::tail ->
    length head = n ->
    store_gpr rs regname val (mk_regs (head ++ val::tail)).

End GPR.


Section AddressResolution.
Inductive reg_rel_addressing addr_bits : regs_state -> reg_name -> int_mod addr_bits -> int_mod addr_bits -> Prop :=
| rca_code_pp: forall regs reg reg_val base ofs
                 abs OF_ignored,
    fetch_gpr regs reg (IntValue reg_val) ->
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
    fetch_gpr regs reg_name value ->
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

End FetchStore.
