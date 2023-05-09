From RecordUpdate Require Import RecordSet.
Require Common Memory Instruction State Addressing.

Import Bool ZArith Addressing Common MemoryBase Memory Instruction State ZMod.

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


  Inductive resolve_fetch_word: regs_state -> execution_frame -> mem_manager -> any -> word_type -> Prop :=
  | rf_resfetch: forall ef mm regs arg loc res,
      resolve ef regs arg loc ->
      fetch_loc regs ef mm loc (FetchPV (IntValue res)) ->
      resolve_fetch_word regs ef mm arg res.


  Inductive update_pc_regular : execution_frame -> execution_frame -> Prop :=
  | fp_update:
    forall pc pc' ef ef',
      fetch_pc ef pc ->
      (pc',false) = uinc_overflow _ pc ->
      update_pc pc ef ef' ->
      update_pc_regular ef ef'.

  (* TODO needs to accept  a list of flags to reset or to keep? *)
  Inductive select_flags: mod_clear_flags -> flags_state -> flags_state -> flags_state -> Prop :=
    | msf_set:
      forall fs fs', select_flags SetFlags fs fs' fs'
    | msf_clr:
      forall fs fs', select_flags PreserveFlags fs fs' fs.


  (**
<<
# Small-step operational instruction semantics

We use a following naming convention:

- when an part of the state is transformed by [step], we version it like that:
  + `name0` for the initial state
  + `name1`, `name2`... for the following states
  + `name'` for the final state.

>>
   *)
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
      fetch_instr regs xstack0 mem_pages {|
                    ins_spec := OpNoOp in1 in2 out1 out2;
                    ins_mods := mk_cmod mod_swap mod_sf;
                    ins_cond := cond
                  |} ->
      cond_activated cond flags ->
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
  (** ** Jump
<<

```
| OpJump (in1:in_any)
```
Assigns a value from `in1` to PC.

### Arguments
>>
- `in1` : any format (see [in_any])
<<

### Modifiers

#### Set Flags

Clears all flags.

### Concerns

- The 'swap' prefix is allowed. It would swap `in1` and `in2`, therefore we would take an address from `in2` (which is regonly). Do we want to explicitly forbid it?
- Currently, `out1` argument is unsupported by assembler but allowed by zkEVM.
>>

   *)
  | step_Jump:
    forall flags0 flags' mod_swap mod_sf contracts mem_pages xstack0 xstack1 xstack' context_u128 in1 
      regs cond word jump_dest,
      let gs := {|
                 gs_flags := flags0;
                 gs_regs := regs;
                 gs_mem_pages := mem_pages;
                 gs_contracts := contracts;
                 gs_callstack := xstack0;
                 gs_context_u128 := context_u128;
               |} in

      fetch_instr regs xstack0 mem_pages {|
                    ins_spec := OpJump in1 ;
                    ins_mods := mk_cmod mod_swap mod_sf;
                    ins_cond := cond
                  |} ->

      cond_activated cond flags0  ->
      resolve_effect__in in1 xstack0 xstack1 ->

      resolve_fetch_word regs xstack1 mem_pages (in_any_incl in1) word ->
      extract_code_address word jump_dest ->
      update_pc jump_dest xstack1 xstack' ->
      step gs
           {|
             gs_flags := flags';
             gs_regs := regs;
             gs_mem_pages := mem_pages;
             gs_contracts := contracts;
             gs_callstack := xstack';
             gs_context_u128 := context_u128;
           |}
(** ** Add


 *)
  | step_Add:
    forall flags0 flags' mod_sf contracts mem_pages mem_pages' xstack0 xstack1 xstack'
      context_u128 in1 in2 out1
      regs regs' cond op1 op2 result new_OF loc_out,
      let gs := {|
                 gs_flags := flags0;
                 gs_regs := regs;
                 gs_mem_pages := mem_pages;
                 gs_contracts := contracts;
                 gs_callstack := xstack0;
                 gs_context_u128 := context_u128;
               |} in

      fetch_instr regs xstack0 mem_pages {|
                    ins_spec := OpAdd in1 in2 out1;
                    ins_mods := mk_cmod NoSwap mod_sf;
                    ins_cond := cond
                  |} ->

      cond_activated cond flags0  ->
      resolve_effect in1 out1 xstack0 xstack1 ->


      resolve_fetch_word regs xstack1 mem_pages (in_any_incl in1) op1 ->
      resolve_fetch_word regs xstack1 mem_pages (in_regonly_incl in2) op2 ->

      uadd_overflow word_bits op1 op2 = (result, new_OF) ->

      let new_OF_LT := if new_OF then Set_OF_LT else Clear_OF_LT in
      let new_EQ := if ZMod.beq _ result zero256 then Set_EQ else Clear_EQ in
      let new_GT := GT_of_bool ( (negb new_EQ) && (negb new_OF_LT) ) in
      let flags1 := mk_fs new_OF_LT new_EQ new_GT in
      select_flags mod_sf flags0 flags1 flags' ->

      resolve xstack1 regs (out_any_incl out1) loc_out ->
      store_loc regs xstack1 mem_pages (IntValue result) loc_out (regs' , mem_pages') ->
      update_pc_regular xstack1 xstack' ->
      step gs
           {|
             gs_flags := flags';
             gs_regs := regs';
             gs_mem_pages := mem_pages';
             gs_contracts := contracts;
             gs_callstack := xstack';
             gs_context_u128 := context_u128;
           |}
           
  | step_Sub:
    forall flags0 flags' mod_sf contracts mem_pages mem_pages' xstack0 xstack1 xstack'
      context_u128 in1 in2 out1
      regs regs' cond op1 op2 result new_OF loc_out,
      let gs := {|
                 gs_flags := flags0;
                 gs_regs := regs;
                 gs_mem_pages := mem_pages;
                 gs_contracts := contracts;
                 gs_callstack := xstack0;
                 gs_context_u128 := context_u128;
               |} in

      fetch_instr regs xstack0 mem_pages {|
                    ins_spec := OpAdd in1 in2 out1;
                    ins_mods := mk_cmod NoSwap mod_sf;
                    ins_cond := cond
                  |} ->

      cond_activated cond flags0  ->
      resolve_effect in1 out1 xstack0 xstack1 ->


      resolve_fetch_word regs xstack1 mem_pages (in_any_incl in1) op1 ->
      resolve_fetch_word regs xstack1 mem_pages (in_regonly_incl in2) op2 ->

      usub_overflow word_bits op1 op2 = (result, new_OF) ->

      let new_OF_LT := if new_OF then Set_OF_LT else Clear_OF_LT in
      let new_EQ := if ZMod.beq _ result zero256 then Set_EQ else Clear_EQ in
      let new_GT := GT_of_bool ( (negb new_EQ) && (negb new_OF_LT) ) in
      let flags1 := mk_fs new_OF_LT new_EQ new_GT in
      select_flags mod_sf flags0 flags1 flags' ->

      resolve xstack1 regs (out_any_incl out1) loc_out ->
      store_loc regs xstack1 mem_pages (IntValue result) loc_out (regs' , mem_pages') ->
      update_pc_regular xstack1 xstack' ->
      step gs
           {|
             gs_flags := flags';
             gs_regs := regs';
             gs_mem_pages := mem_pages';
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
