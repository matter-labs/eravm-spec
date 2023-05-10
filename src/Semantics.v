From RecordUpdate Require Import RecordSet.
Require Common Memory Instruction State MemoryOps.

Import Bool ZArith Common MemoryBase Memory MemoryOps Instruction State ZMod
  ZBits.

Import RecordSetNotations.
#[export] Instance etaXGS : Settable _ :=
  settable! Build_global_state <gs_flags
  ; gs_regs; gs_contracts ; gs_mem_pages; gs_callstack; gs_context_u128>.

(** * Execution *)

Section Execution.
  Import Arg Arg.Coercions.

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


  Inductive update_pc_regular : execution_frame -> execution_frame -> Prop :=
  | fp_update:
    forall pc pc' ef ef',
      fetch_pc ef pc ->
      (pc',false) = uinc_overflow _ pc ->
      update_pc pc ef ef' ->
      update_pc_regular ef ef'.

  Inductive select_flags: mod_set_flags -> flags_state -> flags_state -> flags_state -> Prop :=
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
    (**
<<
## NoOp
```
| OpNoOp (in1: in_any) (in2: in_reg) (out1: out_any) (out2: out_reg)
```

Performs no action.


### Arguments

- `in1` in any format; ignored. May affect SP, see Usage.
- `in2` only in regs; ignored.
- `out1` in any format; ignored. May affect SP, see Usage.
- `in1` in any format; ignored.

### Usage
>>
- Executed when an actual instruction is skipped.

  All instructions are predicated on [cond]. If current flags are not compatible
  with the condition, `noop` is executed instead.

- Adjusting stack pointer.

  The arguments of [OpNoOp] are ignored but the effects of
  [RelativeSPWithPushPop] on SP still take place. For example, consider the
  following instruction:

<<

```coq
Check OpNoOp
(InStack (RelativeSPWithPushPop R1 (u16_of 10%Z)))  (* in1 *)
(RegOnly (Reg R0))                                  (* in2 *)
(OutStack (RelativeSPWithPushPop R2 (u16_of 20%Z))) (* out1 *)
(RegOnly (Reg R0)).                                 (* out2 *)
```

It can be represented as: `NoOp stack-=[10], r0, stack+=20, r0`.


Here, operands `in1` and `out1` are using [RelativeSPWithPushPop] addressing mode.
Therefore, executing this instruction will modify SP like that:

```
sp -= (r1 + 10);
sp += (r2 + 20);
```

TODO: account for Swap modifier
>>
*)
  | step_NoOp:
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

  (** -----
<<
## Jump
```
| OpJump (in1:in_any)
```

>>

Assigns a value from `in1` to PC. The value is truncated to [code_address_bits].

<<
### Arguments

>>

- `in1` : any format (see [in_any])

<<

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

      resolve_fetch_word regs xstack1 mem_pages in1 word ->
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
(** -----
<<
## Add
TODO
>>
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


      resolve_fetch_word regs xstack1 mem_pages in1 op1 ->
      resolve_fetch_word regs xstack1 mem_pages in2 op2 ->

      uadd_overflow word_bits op1 op2 = (result, new_OF) ->

      let new_OF_LT := if new_OF then Set_OF_LT else Clear_OF_LT in
      let new_EQ := if ZMod.beq _ result zero256 then Set_EQ else Clear_EQ in
      let new_GT := GT_of_bool ( (negb new_EQ) && (negb new_OF_LT) ) in
      let flags1 := mk_fs new_OF_LT new_EQ new_GT in
      select_flags mod_sf flags0 flags1 flags' ->

      resolve xstack1 regs out1 loc_out ->
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
(** -----
<<
## Sub
TODO
>>
*)
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
                    ins_spec := OpSub in1 in2 out1;
                    ins_mods := mk_cmod NoSwap mod_sf;
                    ins_cond := cond
                  |} ->

      cond_activated cond flags0  ->
      resolve_effect in1 out1 xstack0 xstack1 ->


      resolve_fetch_word regs xstack1 mem_pages in1 op1 ->
      resolve_fetch_word regs xstack1 mem_pages in2 op2 ->

      usub_overflow word_bits op1 op2 = (result, new_OF) ->

      let new_OF_LT := if new_OF then Set_OF_LT else Clear_OF_LT in
      let new_EQ := if ZMod.beq _ result zero256 then Set_EQ else Clear_EQ in
      let new_GT := GT_of_bool ( (negb new_EQ) && (negb new_OF_LT) ) in
      let flags1 := mk_fs new_OF_LT new_EQ new_GT in
      select_flags mod_sf flags0 flags1 flags' ->

      resolve xstack1 regs out1 loc_out ->
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
(** -----
<<
## Near call

TODO
>>
*)

  | step_NearCall:
    forall flags0 flags' mod_swap mod_sf contracts mem_pages xstack0 xstack1 context_u128 sp
      regs cond abi_params call_addr expt_handler,
      let gs := {|
                 gs_flags := flags0;
                 gs_regs := regs;
                 gs_mem_pages := mem_pages;
                 gs_contracts := contracts;
                 gs_callstack := xstack0;
                 gs_context_u128 := context_u128;
               |} in

      fetch_instr regs xstack0 mem_pages {|
                    ins_spec := OpNearCall abi_params (Imm call_addr) (Imm expt_handler);
                    ins_mods := mk_cmod mod_swap mod_sf;
                    ins_cond := cond
                  |} ->

      cond_activated cond flags0  ->

      update_pc_regular xstack0 xstack1 ->
      fetch_sp xstack1 sp -> (* sp is copied as is*)

      let xstack' := InternalCall (mk_cf expt_handler sp call_addr) xstack1 in
      step gs
           {|
             gs_flags := flags';
             gs_regs := regs;
             gs_mem_pages := mem_pages;
             gs_contracts := contracts;
             gs_callstack := xstack';
             gs_context_u128 := context_u128;
           |}
(** -----
<<
## BinOp (bitwise operations)

TODO
>>
*)

  | step_BinOp:
    forall flags0 flags' mod_sf contracts mem_pages mem_pages' xstack0 xstack1 xstack'
      context_u128 in1 in2 out1
      regs regs' cond op1 op2 result loc_out opmod,
      let gs := {|
                 gs_flags := flags0;
                 gs_regs := regs;
                 gs_mem_pages := mem_pages;
                 gs_contracts := contracts;
                 gs_callstack := xstack0;
                 gs_context_u128 := context_u128;
               |} in

      fetch_instr regs xstack0 mem_pages {|
                    ins_spec := OpBinOp in1 in2 out1 opmod;
                    ins_mods := mk_cmod NoSwap mod_sf;
                    ins_cond := cond
                  |} ->

      cond_activated cond flags0  ->
      resolve_effect in1 out1 xstack0 xstack1 ->


      resolve_fetch_word regs xstack1 mem_pages in1 op1 ->
      resolve_fetch_word regs xstack1 mem_pages in2 op2 ->
      
      binop_func _ opmod op1 op2 = result ->

      let new_EQ := EQ_of_bool (ZMod.beq _ result zero256) in
      select_flags mod_sf flags0 (mk_fs Clear_OF_LT new_EQ Clear_GT) flags' ->

      resolve xstack1 regs out1 loc_out ->
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
 End Execution.
