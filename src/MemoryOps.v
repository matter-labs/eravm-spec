Require Addressing Common Condition ExecutionStack Memory Instruction State.

Import Addressing ZArith ZMod Common Condition ExecutionStack MemoryBase Memory Instruction State List ListNotations.

Inductive endianness := LittleEndian | BigEndian.

(** Location from where a value can be fetched. *)
Inductive loc : Set :=
| LocImm: u16 ->  loc
| LocReg : reg_name ->  loc
| LocStackAddress: stack_address -> loc
| LocCodeAddr: code_address -> loc
| LocConstAddr: const_address ->  loc
| LocHeapAddr: page_id -> mem_address -> loc
| LocAuxHeapAddr: page_id -> mem_address ->  loc.


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

Section Addressing.

  Inductive reg_rel addr_bits : regs_state -> reg_name -> int_mod addr_bits -> int_mod addr_bits -> Prop :=
  | rca_code_pp: forall regs reg reg_val base ofs
                        abs OF_ignored,
      fetch_gpr regs reg = IntValue reg_val ->
      extract_address addr_bits reg_val base ->
      base + ofs = (abs, OF_ignored) ->
      reg_rel addr_bits regs reg ofs abs.

  Definition reg_rel_code : regs_state -> reg_name -> u16 -> code_address -> Prop
    := reg_rel code_address_bits.

  Definition reg_rel_const
    : regs_state -> reg_name -> u16 -> const_address -> Prop
    := reg_rel const_address_bits.

  Definition reg_rel_stack
    : regs_state -> reg_name -> u16 -> stack_address -> Prop
    := reg_rel stack_page_params.(address_bits).

  (** delta = reg + imm *)
  Definition sp_delta_abs: regs_state -> reg_name -> u16 -> stack_address -> Prop := reg_rel_stack.


  Inductive loc_reg: reg_io -> loc ->  Prop :=
  | rslv_reg_aux: forall reg, loc_reg (Reg reg) (LocReg reg).

  Inductive loc_imm: imm_in -> loc ->  Prop :=
  |rslv_imm_aux : forall imm, loc_imm (Imm imm) (LocImm imm).

  Inductive loc_code: regs_state -> code_in -> loc -> Prop :=
  | rslv_code_aux: forall regs reg abs_imm addr,
      reg_rel_code regs reg abs_imm addr ->
      loc_code regs (CodeAddr reg abs_imm) (LocCodeAddr addr).

  Inductive loc_const: regs_state -> const_in -> loc -> Prop :=
  | rslv_const_aux: forall regs reg abs_imm addr,
      reg_rel_const regs reg abs_imm addr ->
      loc_const regs (ConstAddr reg abs_imm) (LocConstAddr addr).

  Inductive loc_stack_io: execution_stack -> regs_state -> stack_io -> loc -> Prop :=
  | rslv_stack_rel_aux: forall ef regs reg offset_imm dlt_sp sp_rel OF_ignore,
      let base := sp_get ef in
      sp_delta_abs regs reg offset_imm dlt_sp ->
      (sp_rel, OF_ignore) = usub_overflow _ base dlt_sp->
      loc_stack_io ef regs (RelSP reg offset_imm) (LocStackAddress sp_rel)
  | rslv_stack_abs_aux: forall ef regs reg imm abs,
      reg_rel_stack regs reg imm abs ->
      loc_stack_io ef regs (Absolute reg imm) (LocStackAddress imm).

  Inductive loc_stack_in_only: execution_stack -> regs_state -> stack_in_only -> loc -> Prop :=
  | rslv_stack_gpop_aux: forall ef regs reg ofs dlt_sp new_sp OF_ignore,
      let sp := sp_get ef in
      sp_delta_abs regs reg ofs dlt_sp ->
      (new_sp, OF_ignore) = usub_overflow _ sp dlt_sp ->
      loc_stack_in_only ef regs (RelSpPop reg ofs) (LocStackAddress new_sp)
  .

  Inductive loc_stack_out_only: execution_stack -> regs_state -> stack_out_only -> loc -> Prop :=
  | rslv_stack_gpush_aux: forall ef regs reg ofs dlt_sp new_sp OF_ignore,
      let sp := sp_get ef in
      sp_delta_abs regs reg ofs dlt_sp ->
      (new_sp, OF_ignore) = sp + dlt_sp ->
      loc_stack_out_only ef regs (RelSpPush reg ofs) (LocStackAddress new_sp)
  .

  Inductive resolve: execution_stack -> regs_state -> any -> loc -> Prop :=
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

  Inductive resolve_effect__in: in_any -> execution_stack -> execution_stack -> Prop :=
  | rslv_stack_in_effect: forall ef ef' regs sp' reg ofs arg,
      loc_stack_in_only ef regs  arg (LocStackAddress sp') ->
      sp_mod_spec (fun _ => sp') ef ef' ->
      resolve_effect__in  (InStack (StackInOnly (RelSpPop reg ofs)))  ef ef'
  | rslv_stack_in_effect_none: forall ef arg,
      (forall reg ofs, arg <> InStack (StackInOnly (RelSpPop reg ofs))) ->
      resolve_effect__in  arg  ef ef.

  Inductive resolve_effect__out: out_any -> execution_stack -> execution_stack -> Prop :=
  | rslv_stack_out_effect: forall ef ef' regs sp' reg ofs arg,
      loc_stack_out_only ef regs  arg (LocStackAddress sp') ->
      sp_mod_spec (fun _ => sp') ef ef' ->
      resolve_effect__out  (OutStack (StackOutOnly (RelSpPush reg ofs)))  ef ef'
  | rslv_stack_out_effect_none: forall ef arg,
      (forall reg ofs, arg <> OutStack (StackOutOnly (RelSpPush reg ofs))) ->
      resolve_effect__out  arg  ef ef.

  (**
If in instruction `in1` is using [RelSpPop] And `out1` is using [RelSpPush], then both
 effects are applied in order:

- first, the `in` effect,
- then, the `out` effect.
- then, if the instruction accesses SP, it will observe the value after both effects are applied.

See an example in [sem.ModSP.step].
   *)
  Inductive resolve_effect: in_any -> out_any -> execution_stack -> execution_stack -> Prop :=
  | rslv_effect_full: forall arg1 arg2 ef1 ef2 ef3,
      resolve_effect__in arg1 ef1 ef2 ->
      resolve_effect__out arg2 ef2 ef3 ->
      resolve_effect arg1 arg2 ef1 ef3.

End Addressing.

Section FetchStore.

  Inductive fetch_result : Set :=
  | FetchIns (ins :instruction_predicated)
  | FetchPV (pv: primitive_value) .

  (* Address resolution *)
  Inductive fetch_loc: regs_state -> execution_stack -> pages -> loc -> fetch_result -> Prop :=
  | fetch_reg:
    forall regs ef mm reg_name,
      fetch_loc regs ef mm (LocReg reg_name) (FetchPV (fetch_gpr regs reg_name))

  | fetch_imm:
    forall regs ef mm imm imm',
      imm' = resize _ word_bits imm ->
      fetch_loc regs ef mm (LocImm imm) (FetchPV (IntValue imm'))

  | fetch_stackaddr:
    forall regs ef ps stackpage addr value,
      active_stackpage ps ef (StackPage _ _ stackpage) ->
      load_result _ addr stackpage value ->
      fetch_loc regs ef ps (LocStackAddress addr) (FetchPV value)
  | fetch_codeaddr:
    forall regs ef ps codepage addr ins,
      active_codepage ps ef (CodePage _ _ codepage) ->
      load_result _ addr codepage ins ->
      fetch_loc regs ef ps (LocCodeAddr addr) (FetchIns ins)
  | fetch_constaddr:
    forall regs ef ps constpage addr value,
      active_codepage ps ef (ConstPage _ _ constpage) ->
      load_result _ addr constpage value ->
      fetch_loc regs ef ps (LocConstAddr addr) (FetchPV (IntValue value))
  .

  Definition load_word (e: endianness) (mem:data_page) (addr:mem_address) :option word :=
    match load_multicell data_page_params addr bytes_in_word mem with
    | None => None
    | Some val =>
        let fend : list u8 -> list u8 := match e with
                                        | LittleEndian => @List.rev u8
                                        | BigEndian => id
                                        end in
        Some (merge_bytes bits_in_byte word_bits (fend val))
    end
  .

  Definition load_slice_word (e:endianness) (mem:data_slice) (addr:mem_address) :option word :=
    match load_multicell data_page_slice_params addr bytes_in_word mem with
    | None => None
    | Some val =>
        let fend : list u8 -> list u8 := match e with
                                        | LittleEndian => @List.rev u8
                                        | BigEndian => id
                                        end in
        Some (merge_bytes bits_in_byte word_bits (fend val))
    end.
  
  Inductive load_result : endianness -> data_page -> mem_address -> word -> Prop :=
  | ldr_apply: forall (mem:data_page) (addr:mem_address) e res,
      load_word e mem addr = Some res ->
      load_result e mem addr res.

  Inductive load_slice_result : endianness -> data_slice -> mem_address -> word -> Prop :=
  | lsr_apply: forall (mem:data_slice) (addr:mem_address) res e,
      load_slice_word e mem addr = Some res ->
      load_slice_result e mem addr res.
  
  Inductive fetch_instr : regs_state -> execution_stack -> pages -> instruction_predicated -> Prop :=
  | fi_fetch: forall regs ef mm ins,
      fetch_loc regs ef mm (LocCodeAddr (pc_get ef)) (FetchIns ins) ->
      fetch_instr regs ef mm ins.

  Inductive store_loc: regs_state -> execution_stack -> pages -> primitive_value -> loc -> (regs_state * pages) -> Prop :=
  | store_reg:
    forall regs regs' ef mm reg_name value,
      store_gpr regs reg_name value regs' ->
      store_loc regs ef mm value (LocReg reg_name) (regs', mm)

  | store_stackaddr:
    forall regs ef ps ps' stackpage addr value pid stackpage',
      active_stackpage ps ef (StackPage _ _ stackpage) ->
      store_result _ addr stackpage value stackpage' ->
      page_replace pid (StackPage _ _ stackpage') ps ps' ->
      store_loc regs ef ps value (LocStackAddress addr) (regs, ps')
  .
  


  Definition store_word (e:endianness) (mem:data_page) (addr:mem_address) (val: word) : option data_page :=
    let ls := match e with
              | LittleEndian => word_to_bytes val
              | BigEndian => rev (word_to_bytes val)
              end in
    store_multicell _ addr ls mem.

  Inductive store_word_result: endianness -> data_page -> mem_address -> word -> data_page -> Prop :=
  | sdr_apply :
    forall e page addr val page',
      store_word e page addr val = Some page' ->
      store_word_result e page addr val page'.
  
  Inductive resolve_fetch_value: regs_state -> execution_stack -> pages -> any -> primitive_value -> Prop :=
  | rf_resfetch_pv: forall ef mm regs arg loc res,
      resolve ef regs arg loc ->
      fetch_loc regs ef mm loc (FetchPV res) ->
      resolve_fetch_value regs ef mm arg res.

  Inductive resolve_fetch_word: regs_state -> execution_stack -> pages -> any -> word -> Prop :=
  | rf_resfetch_w: forall ef mm regs arg res,
      resolve_fetch_value regs ef mm arg (IntValue res) ->
      resolve_fetch_word regs ef mm arg res.


  Inductive resolve_store: regs_state -> execution_stack -> pages
                           -> out_any -> primitive_value -> regs_state * pages
                           -> Prop :=
  | rs_resstore: forall ef mm regs arg loc_out pv regs' mm',
      resolve ef regs (out_any_incl arg) loc_out ->
      store_loc regs ef mm pv loc_out (regs', mm') ->
      resolve_store regs ef mm arg pv (regs', mm').

End FetchStore.
