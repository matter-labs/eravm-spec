Require Common Memory Instruction State.

Import ZArith ZMod Common MemoryBase Memory Instruction State Arg.

(** Location from where a value can be fetched. *)
Inductive loc : Set :=
| LocImm: u16 ->  loc
| LocReg : reg_name ->  loc
| LocStackAddress: stack_address -> loc
| LocCodeAddr: code_address -> loc
| LocConstAddr: const_address ->  loc
| LocHeapAddr: mem_page_id -> mem_address -> loc
| LocAuxHeapAddr: mem_page_id -> mem_address ->  loc.




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

(* Resolve any location except when addressing with [RelativeSPWithPushPop].
  Since in that addressing mode *)

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

Inductive loc_stack_io: regs_state -> stack_io -> loc -> Prop :=
| rslv_stack_rel_aux: forall regs reg base offset_imm dlt_sp sp_rel OF_ignore,
    fetch_sp regs base ->
    sp_delta_abs regs reg offset_imm dlt_sp ->
    (sp_rel, OF_ignore) = usub_overflow _ base dlt_sp->
    loc_stack_io regs (RelSP reg offset_imm) (LocStackAddress sp_rel)
| rslv_stack_abs_aux: forall regs reg imm abs,
    reg_rel_stack_addressing regs reg imm abs ->
    loc_stack_io regs (Absolute reg imm) (LocStackAddress imm).

Inductive loc_stack_in_only: regs_state -> stack_in_only -> loc -> Prop :=
| rslv_stack_gpop_aux: forall regs reg sp ofs dlt_sp new_sp OF_ignore,
    fetch_sp regs sp ->
    sp_delta_abs regs reg ofs dlt_sp ->
    (new_sp, OF_ignore) = usub_overflow _ sp dlt_sp ->
    loc_stack_in_only regs (RelSpPop reg ofs) (LocStackAddress new_sp)
.

Inductive loc_stack_out_only: regs_state -> stack_out_only -> loc -> Prop :=
| rslv_stack_gpush_aux: forall regs reg sp ofs dlt_sp new_sp OF_ignore,
    fetch_sp regs sp ->
    sp_delta_abs regs reg ofs dlt_sp ->
    (new_sp, OF_ignore) = uadd_overflow _ sp dlt_sp ->
    loc_stack_out_only regs (RelSpPush reg ofs) (LocStackAddress new_sp)
.

Inductive resolve: regs_state -> any -> loc -> Prop :=
| rslv_reg : forall rs r loc,
    loc_reg r loc ->
    resolve rs (AnyReg r) loc
| rslv_imm: forall rs imm loc,
    loc_imm imm loc ->
    resolve rs (AnyImm imm) loc
| rslv_stack_io: forall regs arg loc,
    loc_stack_io regs arg loc ->
    resolve regs (AnyStack (StackAnyIO arg)) loc
| rslv_stack_in: forall regs arg loc,
    loc_stack_in_only regs arg loc ->
    resolve regs (AnyStack (StackAnyIn arg)) loc
| rslv_stack_out: forall regs arg loc,
    loc_stack_out_only regs arg loc ->
    resolve regs (AnyStack (StackAnyOut arg)) loc
| rslv_code: forall regs arg loc,
    loc_code regs arg loc ->
    resolve regs (AnyCode arg) loc
| rslv_const: forall regs arg loc,
    loc_const regs arg loc ->
    resolve regs (AnyConst arg) loc
.

Inductive resolve_effect__in: regs_state -> in_any -> regs_state -> Prop :=
| rslv_stack_in_effect: forall gprs sp pc sp' reg ofs arg,
    loc_stack_in_only (mk_regs gprs sp pc) arg (LocStackAddress sp') ->
    resolve_effect__in (mk_regs gprs sp pc) (InStack (StackInOnly (RelSpPop reg ofs))) (mk_regs gprs sp' pc).

Inductive resolve_effect__out: regs_state -> out_any -> regs_state -> Prop :=
| rslv_stack_out_effect: forall gprs sp pc sp' reg ofs arg,
    loc_stack_out_only (mk_regs gprs sp pc) arg (LocStackAddress sp') ->
    resolve_effect__out (mk_regs gprs sp pc) (OutStack (StackOutOnly (RelSpPush reg ofs))) (mk_regs gprs sp' pc).

Inductive resolve_effect: in_any -> out_any -> regs_state -> regs_state -> Prop :=
| rslv_effect_full: forall arg1 arg2 regs1 regs2 regs3,
    resolve_effect__in regs1 arg1 regs2 ->
    resolve_effect__out regs2 arg2 regs3 ->
    resolve_effect arg1 arg2 regs1 regs3.
