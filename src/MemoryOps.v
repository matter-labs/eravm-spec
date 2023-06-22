From RecordUpdate Require Import RecordSet.

Require Addressing Common Condition CallStack Error Memory Instruction.

Import Addressing ZArith ZMod Common Condition CallStack MemoryBase Memory Instruction Pages List ListNotations Error String.
Import RecordSetNotations.
Open Scope error_monad_scope.

Inductive endianness := LittleEndian | BigEndian.

(** Location from where a value can be fetched. *)
Inductive loc : Set :=
| LocImm: u16 ->  loc
| LocReg : reg_name ->  loc
| LocStackAddress: stack_address -> loc
| LocCodeAddr: code_address -> loc
| LocConstAddr: const_address ->  loc
(* | LocHeapVariantAddr: page_id -> mem_address -> loc *)
.

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


Definition do_store_gpr (r: regs_state) (rn: reg_name) (pv: primitive_value) : res regs_state :=
  match rn with
    | R0 => Error (msg "Can not store register R0 is read only")
  | R1 => OK (r <| gprs_r1 := pv|>)
  | R2 => OK (r <| gprs_r2 := pv|>)
  | R3 => OK (r <| gprs_r3 := pv|>)
  | R4 => OK (r <| gprs_r4 := pv|>)
  | R5 => OK (r <| gprs_r5 := pv|>)
  | R6 => OK (r <| gprs_r6 := pv|>)
  | R7 => OK (r <| gprs_r7 := pv|>)
  | R8 => OK (r <| gprs_r8 := pv|>)
  | R9 => OK (r <| gprs_r9 := pv|>)
  | R10 => OK (r <| gprs_r10 := pv|>)
  | R11 => OK (r <| gprs_r11 := pv|>)
  | R12 => OK (r <| gprs_r12 := pv|>)
  | R13 => OK (r <| gprs_r13 := pv|>)
  | R14 => OK (r <| gprs_r14 := pv|>)
  | R15 => OK (r <| gprs_r15 := pv|>)
  end.
                                                          
  Definition store_gpr_correct:
    forall regs rn pv regs',
    store_gpr regs rn pv regs' ->
    do_store_gpr regs rn pv = OK regs'.
  Proof. destruct 1; constructor. Qed.
  
    
End GPR.


  
Section Addressing.

  Inductive reg_rel addr_bits : regs_state -> reg_name -> int_mod addr_bits -> int_mod addr_bits -> Prop :=
  | rca_code_pp: forall regs reg reg_val base ofs
                        abs OF_ignored,
      fetch_gpr regs reg = IntValue reg_val ->
      extract_address addr_bits reg_val base ->
      base + ofs = (abs, OF_ignored) ->
      reg_rel addr_bits regs reg ofs abs.

  Definition do_reg_rel {addr_bits} (rs: regs_state) (r: reg_name) (ofs: int_mod addr_bits) :  res( int_mod addr_bits) :=
      match fetch_gpr rs r with
       | IntValue reg_val =>
           OK (add_wrap _ (resize _ addr_bits reg_val) ofs)
      |_ => Error (msg "Expected a non-pointer value in register")
      end.

  Theorem reg_rel_spec :
    forall addr_bits rs r ofs abs,
      @reg_rel addr_bits rs r ofs abs ->
      @do_reg_rel addr_bits rs r ofs = OK abs.
  Proof.
    intros addr_bits rs r ofs abs H.
    inv H.
    inv H2.
    inv H1.
    unfold do_reg_rel, resize, add_wrap, uadd_overflow, as_unsigned in *.
    rewrite H0; auto.
  Qed.
  
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

  Inductive loc_stack_io: callstack -> regs_state -> stack_io -> loc -> Prop :=
  | rslv_stack_rel_aux: forall ef regs reg offset_imm dlt_sp sp_rel OF_ignore,
      let base := sp_get ef in
      sp_delta_abs regs reg offset_imm dlt_sp ->
      (sp_rel, OF_ignore) = base - dlt_sp->
      loc_stack_io ef regs (RelSP reg offset_imm) (LocStackAddress sp_rel)
                   
  | rslv_stack_abs_aux: forall ef regs reg imm abs,
      reg_rel_stack regs reg imm abs ->
      loc_stack_io ef regs (Absolute reg imm) (LocStackAddress abs).

(* FIXME of should not be ignored*)
  Inductive loc_stack_in_only: callstack -> regs_state -> stack_in_only -> loc -> Prop :=
  | rslv_stack_gpop_aux: forall ef regs reg ofs dlt_sp new_sp OF_ignore,
      let sp := sp_get ef in
      sp_delta_abs regs reg ofs dlt_sp ->
      (new_sp, OF_ignore) = sp - dlt_sp ->
      loc_stack_in_only ef regs (RelSpPop reg ofs) (LocStackAddress new_sp)
  .
(* FIXME of should not be ignored*)
  Inductive loc_stack_out_only: callstack -> regs_state -> stack_out_only -> loc -> Prop :=
  | rslv_stack_gpush_aux: forall ef regs reg ofs dlt_sp new_sp OF_ignore,
      let sp := sp_get ef in
      sp_delta_abs regs reg ofs dlt_sp ->
      (new_sp, OF_ignore) = sp + dlt_sp ->
      loc_stack_out_only ef regs (RelSpPush reg ofs) (LocStackAddress new_sp)
  .

  Inductive resolve: callstack -> regs_state -> any -> loc -> Prop :=
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

                      
  Definition do_resolve (xstack: callstack) (rs:regs_state) (a:any) : res loc :=
    match a with
    | AnyReg (Reg r) => OK (LocReg r)
    | AnyImm (Imm i) => OK (LocImm i)
    | AnyStack (StackAnyIO (Absolute r ofs)) =>
        do abs <- do_reg_rel rs r ofs ;
        OK (LocStackAddress abs)
    | AnyStack (StackAnyIO (RelSP r ofs)) =>  
        do sp_ofs <- do_reg_rel rs r ofs ;
        let abs := sub_wrap _ (sp_get xstack) sp_ofs in
        OK (LocStackAddress abs)
    | AnyStack (StackAnyIn (RelSpPop r ofs)) =>
        do sp_ofs <- do_reg_rel rs r ofs ;
        let abs := sub_wrap _ (sp_get xstack) sp_ofs in
        OK (LocStackAddress abs)
                  
    | AnyStack (StackAnyOut (RelSpPush r ofs)) =>
        do sp_ofs <- do_reg_rel rs r ofs ;
        let abs := add_wrap _ (sp_get xstack) sp_ofs in
        OK (LocStackAddress abs)
    | AnyCode (CodeAddr r ofs) =>
        do abs <- do_reg_rel rs r ofs ;
        OK (LocCodeAddr abs)
    | AnyConst (ConstAddr r ofs) => 
        do abs <- do_reg_rel rs r ofs ;
        OK (LocConstAddr abs)
    end .

  Theorem do_resolve_correct:
    forall xstack rs a res,
      resolve xstack rs a res ->
      do_resolve xstack rs a = OK res.
  Proof.
{
  intros xstack rs [] res; inversion_clear 1; subst; simpl.
  - destruct r;  auto; inversion_clear H0; auto.
  - destruct i;  auto; inversion_clear H0; auto.
  - inversion_clear H0.
    + inv H.
      exploit (reg_rel_spec (address_bits stack_page_params)).
      * econstructor; eauto.
      * intro H'.
        simpl in *. rewrite H'.
        simpl.
        inv H3.
        inv H1.
        repeat f_equal.
    +  inv H.
       unfold do_reg_rel.
       rewrite H0.
       unfold add_wrap, uadd_overflow in *.
       inv H2.
       inv H1.
       simpl.
       repeat f_equal.
  - inv H0.
    inv H.
    inv H0.
    inv H2.
    inv H3.
    unfold do_reg_rel.
    rewrite H4.
    unfold add_wrap, uadd_overflow, sub_wrap, usub_overflow in *.
    simpl.
    inv H1.
    reflexivity.
  - inv H0.   
    inv H.   
    inv H1.
    inv H3.
    inv H2.
    unfold do_reg_rel.
    rewrite H0.
    reflexivity.
  - inv H0.
    inv H.
    inv H2.
    inv H1.
    unfold do_reg_rel.
    rewrite H0.
    reflexivity.
  - inv H0.
    inv H.
    inv H2.
    inv H1.
    unfold do_reg_rel.
    rewrite H0.
    reflexivity.
}
  Qed.

  
  Inductive resolve_effect__in: in_any -> callstack -> callstack -> Prop :=
  | rslv_stack_in_effect: forall ef ef' regs sp' reg ofs arg,
      loc_stack_in_only ef regs  arg (LocStackAddress sp') ->
      sp_mod_spec (fun _ => sp') ef ef' ->
      resolve_effect__in  (InStack (StackInOnly (RelSpPop reg ofs)))  ef ef'
  | rslv_stack_in_effect_none: forall ef arg,
      (forall reg ofs, arg <> InStack (StackInOnly (RelSpPop reg ofs))) ->
      resolve_effect__in  arg  ef ef.

  Inductive resolve_effect__out: out_any -> callstack -> callstack -> Prop :=
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
  Inductive resolve_effect: in_any -> out_any -> callstack -> callstack -> Prop :=
  | rslv_effect_full: forall arg1 arg2 ef1 ef2 ef3,
      resolve_effect__in arg1 ef1 ef2 ->
      resolve_effect__out arg2 ef2 ef3 ->
      resolve_effect arg1 arg2 ef1 ef3.

End Addressing.

Section FetchStore.

  Context {instruction: Type} (inv: instruction).
 
  Let memory := Pages.memory instruction_invalid.
  Inductive fetch_result : Set :=
  | FetchIns (ins :instruction_predicated)
  | FetchPV (pv: primitive_value) .

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
  
  (* Address resolution *)
  Inductive fetch_loc: regs_state -> callstack -> memory -> loc -> fetch_result -> Prop :=
  | fetch_reg:
    forall regs ef mm reg_name,
      fetch_loc regs ef mm (LocReg reg_name) (FetchPV (fetch_gpr regs reg_name))

  | fetch_imm:
    forall regs ef mm imm imm',
      imm' = resize _ word_bits imm ->
      fetch_loc regs ef mm (LocImm imm) (FetchPV (IntValue imm'))

  | fetch_stackaddr:
    forall regs ef ps stackpage addr value,
      active_stackpage _ ps ef (StackPage _ stackpage) ->
      MemoryBase.load_result _ addr stackpage value ->
      fetch_loc regs ef ps (LocStackAddress addr) (FetchPV value)
  | fetch_codeaddr:
    forall regs ef ps codepage addr ins,
      active_codepage _ ps ef (CodePage _ codepage) ->
      MemoryBase.load_result _ addr codepage ins ->
      fetch_loc regs ef ps (LocCodeAddr addr) (FetchIns ins)
  | fetch_constaddr:
    forall regs ef ps constpage addr value,
      active_codepage _ ps ef (ConstPage _ constpage) ->
      MemoryBase.load_result _ addr constpage value ->
      fetch_loc regs ef ps (LocConstAddr addr) (FetchPV (IntValue value))

                
  (*   forall regs ef ps dp pid addr value, *)
  (*     page_has_id _ ps pid (DataPage _ dp) -> *)
  (*     load_result BigEndian dp addr value -> *)
  (*     fetch_loc regs ef ps (LocHeapVariantAddr pid addr) (FetchPV (IntValue value)) *)
  .

  
  Inductive fetch_instr : regs_state -> callstack -> memory -> instruction_predicated -> Prop :=
  | fi_fetch: forall regs ef mm ins,
      fetch_loc regs ef mm (LocCodeAddr (pc_get ef)) (FetchIns ins) ->
      fetch_instr regs ef mm ins.

  Inductive store_loc: regs_state -> callstack -> memory -> primitive_value -> loc -> (regs_state * memory) -> Prop :=
  | store_reg:
    forall regs regs' ef mm reg_name value,
      store_gpr regs reg_name value regs' ->
      store_loc regs ef mm value (LocReg reg_name) (regs', mm)

  | store_stackaddr:
    forall regs ef ps ps' stackpage addr value pid stackpage',
      active_stackpage _ ps ef (StackPage _ stackpage) ->
      store_result _ addr stackpage value stackpage' ->
      page_replace _ pid (StackPage _ stackpage') ps ps' ->
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
  
  Inductive resolve_load: callstack -> (regs_state * memory) -> any -> primitive_value -> Prop :=
  | rf_resfetch_pv: forall ef mm regs arg loc res,
      resolve ef regs arg loc ->
      fetch_loc regs ef mm loc (FetchPV res) ->
      resolve_load ef (regs , mm) arg res.

  Inductive resolve_loads: callstack -> (regs_state * memory)
                            -> list (in_any * primitive_value) 
                            -> Prop :=
  | rsl_nil: forall ef s ,
      resolve_loads ef s nil
                    
  | rsl_cons: forall ef regs memory (arg:in_any) pv (tail: list (in_any*primitive_value)),
      resolve_loads ef (regs, memory) tail ->
      resolve_load  ef (regs, memory ) (in_any_incl arg) pv ->
      resolve_loads ef (regs, memory ) ((arg,pv)::tail).

  
  Inductive resolve_load_word: callstack -> regs_state * memory -> any -> word -> Prop :=
  | rf_resfetch_w: forall ef s arg res,
      resolve_load ef s arg (IntValue res) ->
      resolve_load_word ef s arg res.

  Inductive resolve_load_words: callstack -> (regs_state * memory)
                            -> list (in_any * word) 
                            -> Prop :=
  | rslw_nil: forall ef s ,
      resolve_load_words ef s nil
                    
  | rslw_cons: forall ef regs memory (arg:in_any) pv (tail: list (in_any*word)),
      resolve_load_words ef (regs, memory) tail ->
      resolve_load_word ef (regs, memory ) (in_any_incl arg) pv ->
      resolve_load_words ef (regs, memory ) ((arg,pv)::tail).

  Inductive resolve_store: callstack -> (regs_state * memory)
                           -> out_any -> primitive_value -> regs_state * memory
                           -> Prop :=
  | rs_resstore: forall ef mm regs arg loc_out pv regs' mm',
      resolve ef regs (out_any_incl arg) loc_out ->
      store_loc regs ef mm pv loc_out (regs', mm') ->
      resolve_store ef (regs, mm) arg pv (regs', mm').

  Inductive resolve_stores: callstack -> (regs_state * memory)
                            -> list (out_any * primitive_value) -> (regs_state * memory)
                            -> Prop :=
  | rss_nil: forall ef s ,
      resolve_stores ef s nil s
  | rss_cons: forall ef regs memory regs' memory' regs'' memory'' out pv tail,
      resolve_stores ef (regs', memory') tail (regs'', memory'') ->
      resolve_store ef (regs,memory) out pv (regs', memory') ->
      resolve_stores ef (regs, memory) (cons (out,pv) tail)  (regs'', memory'').

  Record fqa_storage := mk_fqa_storage {
                        k_shard: shard_id;
                        k_contract: contract_address;
                        }.
  Record fqa_key := mk_fqa_key {
                        k_storage :> fqa_storage;
                        k_key: storage_address
                        }.

  Inductive storage_get (d: depot): fqa_storage -> storage -> Prop :=
  | sg_apply: forall storage shard s c st,
      shard_exists s ->
      MemoryBase.load_result depot_params s d shard ->
      MemoryBase.load_result shard_params c shard storage  ->
      storage_get d (mk_fqa_storage s c) st .
  
  Inductive storage_read (d: depot): fqa_key -> word -> Prop :=
  | sr_apply: forall storage sk c w,
      storage_get d sk storage -> 
      storage_read d (mk_fqa_key sk c) w.
  
  Inductive storage_write (d: depot): fqa_key -> word -> depot -> Prop :=
  | sw_apply: forall storage shard sk s c k w  shard' depot' storage',
      storage_get d sk storage -> 
      MemoryBase.store_result storage_params k storage w storage' ->
      MemoryBase.store_result shard_params c shard storage' shard'  ->
      MemoryBase.store_result depot_params s d shard' depot' ->
      storage_write d (mk_fqa_key sk k) w depot'.

End FetchStore.
 
