Require Core Addressing CallStack .

Import Addressing Core Common ZArith ZMod CallStack GPR Memory PrimitiveValue.

Section AddressingUtils.
  Import MemoryBase.
  Open Scope ZMod_scope.
  Definition extract_stack_address: word -> stack_address -> Prop := extract_address _.
  Definition extract_code_address: word -> code_address -> Prop := extract_address _.
  Definition extract_const_address: word -> const_address -> Prop := extract_address _.

  Inductive reg_rel addr_bits : regs_state -> reg_name -> int_mod addr_bits -> int_mod addr_bits -> Prop :=
  | rca_code_pp: forall regs reg reg_val base ofs
                   abs OF_ignored,
      fetch_gpr regs reg = IntValue reg_val ->
      extract_address addr_bits reg_val base ->
      base + ofs = (abs, OF_ignored) ->
      reg_rel addr_bits regs reg ofs abs.

  Definition reg_rel_code : regs_state -> reg_name -> u16 -> code_address -> Prop
    := reg_rel code_address_bits.
  Definition reg_rel_const : regs_state -> reg_name -> u16 -> const_address -> Prop
    := reg_rel const_address_bits.
  Definition reg_rel_stack : regs_state -> reg_name -> u16 -> stack_address -> Prop
    := reg_rel stack_page_params.(address_bits).

  (** delta = reg + imm *)
  Definition sp_displ: regs_state -> reg_name -> u16 -> stack_address -> Prop := reg_rel_stack.
End AddressingUtils.

Inductive loc : Set :=
| LocImm: u16 ->  loc
| LocReg : reg_name ->  loc
| LocStackAddress: stack_address -> loc
| LocCodeAddr: code_address -> loc
| LocConstAddr: const_address ->  loc
.


Section Resolve.
  Import Addressing.Coercions.
  
  Open Scope ZMod_scope.
  
  Inductive resolve_effect := | NoEffect | NewSP (val: stack_address).
  
  Record resolve_result :=
    mk_resolved {
        effect: resolve_effect;
        location:> loc;
      }.
  
  Context {state_checkpoint}
    (callstack := @callstack state_checkpoint)
    (rs:regs_state)
    (cs: callstack)
    (sp:= sp_get cs).
  
  Reserved Notation "[[ resolved ]]" (at level 9, no associativity).
  Reserved Notation "[[ resolved ; 'SP' <- newsp ]]" (at level 9, no associativity).

  Declare Scope Resolution_scope.
  Open Scope Resolution_scope.

  Inductive resolve : any -> resolve_result -> Prop :=
  
  | rslv_reg : forall reg,
      resolve (Reg reg) [[ LocReg reg ]]
  | rslv_imm: forall imm,
      resolve  (Imm imm) [[ LocImm imm ]]
              
  | rslv_stack_rel: forall reg ofs delta_sp sp_rel,
      sp_displ rs reg ofs delta_sp ->
      
      (sp_rel, false) = sp - delta_sp->
      resolve  (RelSP reg ofs) [[ LocStackAddress sp_rel ]]

  | rslv_stack_abs: forall regs reg imm abs,
      reg_rel_stack regs reg imm abs ->
      resolve  (Absolute reg imm) [[ LocStackAddress abs ]]

  | rslv_stack_gpop: forall reg ofs delta_sp new_sp,
      sp_displ rs reg ofs delta_sp ->
      (new_sp, false) = sp - delta_sp->
      resolve  (RelSpPop reg ofs) [[ LocStackAddress new_sp ; SP <- new_sp ]]
              
  | rslv_stack_gpush: forall reg ofs delta_sp new_sp,
      sp_displ rs reg ofs delta_sp ->
      (new_sp, false) = sp + delta_sp ->
      resolve  (RelSpPush reg ofs) [[ LocStackAddress sp ; SP <- new_sp ]]
              
  | rslv_code: forall reg abs_imm addr,
      reg_rel_code rs reg abs_imm addr ->
      resolve  (CodeAddr reg abs_imm) [[ LocCodeAddr addr ]]
  | rslv_const: forall reg abs_imm addr,
      reg_rel_const rs reg abs_imm addr ->
      resolve  (ConstAddr reg abs_imm) [[ LocConstAddr addr ]]
  where 
  "[[ resolved ]]" := (mk_resolved NoEffect resolved) : Resolution_scope
  and
  "[[ resolved ; 'SP' <- newsp ]]" := (mk_resolved (NewSP newsp) resolved) : Resolution_scope.

  Inductive apply_effects : resolve_effect -> callstack -> Prop :=
  | ae_none: forall s,
      apply_effects NoEffect s
  | ae_sp: forall  cs' new_sp,
      cs' = sp_mod (fun _ => new_sp) cs ->
      apply_effects (NewSP new_sp) cs'.
  
  Inductive resolve_apply
    : any -> (callstack * loc) -> Prop :=
  | ra_no_effect : forall arg loc,
      resolve arg [[ loc ]] ->
      resolve_apply arg (cs, loc)
  | ra_effect : forall cs' arg loc new_sp,
      resolve arg [[ loc ; SP <- new_sp ]] ->
      cs' = sp_mod (fun _ => new_sp) cs ->
      resolve_apply arg (cs', loc).
  
End Resolve. 



  (**
If in instruction `in1` is using [RelSpPop] And `out1` is using [RelSpPush], then both
effects are applied in order:

- first, the `in` effect,
- then, the `out` effect.
- then, if the instruction accesses SP, it will observe the value after both effects are applied.

See an example in [sem.ModSP.step].
   *)

