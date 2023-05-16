From RecordUpdate Require Import RecordSet.
Require Common Memory Instruction State MemoryOps ABI.

Import Bool ZArith Common MemoryBase Memory MemoryOps Instruction State ZMod
  ZBits ABI.

Import RecordSetNotations.
#[export] Instance etaXGS : Settable _ := settable! Build_global_state <gs_flags
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
      uinc_overflow _ pc = (pc',false) ->
      update_pc pc' ef ef' ->
      update_pc_regular ef ef'.

  Definition apply_swap {T} (md: mod_swap) (a b:T) : T*T :=
    match md with
    | NoSwap => (a,b)
    | Swap => (b,a)
    end.

  Definition apply_set_flags (md: mod_set_flags) (f f':flags_state) : flags_state :=
    match md with
    | SetFlags => f'
    | PreserveFlags => f
    end.

(*
    let mut ergs_cost =
        zkevm_opcode_defs::OPCODES_PRICES[opcode_raw_variant_idx.into_usize()] as u32;
    if skip_cycle {
        // we have already paid for it
        ergs_cost = 0;
    }

    let (mut ergs_remaining, not_enough_power) = local_state
        .callstack
        .get_current_stack()
        .ergs_remaining
        .overflowing_sub(ergs_cost);
    if not_enough_power {
        ergs_remaining = 0;
        error_flags.set(ErrorFlags::NOT_ENOUGH_ERGS, true);
    }

    delayed_changes.new_ergs_remaining = Some(ergs_remaining);
*)
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

- `in1`, any format; ignored. May affect SP, see Usage.
- `in2`, reg only; ignored.
- `out1`, any format; ignored. May affect SP, see Usage.
- `out2`, reg only; ignored.

### Modifiers
- `swap` has no effect
- `set_flags` has no effect


### Usage
>>
- Executed when an actual instruction is skipped.

  All instructions are executed conditionally; this is formalized by [cond].
  If current flags are not compatible with the condition, [OpNoOp] is executed instead.

- Adjusting stack pointer.

  The arguments of [OpNoOp] are ignored but the effects of
  [RelSpPush]/[RelSpPop] on SP still take place.



<<
#### Example of adjusting SP using [OpNoOp]

Consider the instruction `NoOp stack-=[10], r0, stack+=20, r0`.
It can be constructed as follows:

```coq
Check OpNoOp (RelSpPop R1 (u16_of 10%Z))  (* in1 *)
(Reg R0)                                  (* in2 *)
(RelSpPush R2 (u16_of 20%Z))              (* out1 *)
(Reg R0).                                 (* out2 *)
```

In this instruction:

- the operand `in1` is using the [RelSpPop] addressing mode
- the operand `out1` is using [RelSpPush] addressing mode.

Therefore, executing this instruction will modify SP like that:

```
sp -= (r1 + 10);
sp += (r2 + 20);
```

>>
*)
  | step_NoOp:
    forall flags mods contracts mem_pages xstack0 xstack1 xstack' context_u128 in1 in2 out1 out2 regs cond ergs_left,

      cond_activated cond flags ->

      let ins := OpNoOp in1 in2 out1 out2 in
      fetch_instr regs xstack0 mem_pages
                  {|
                    ins_spec := ins;
                    ins_mods := mods;
                    ins_cond := cond
                  |} ->

      update_pc_regular xstack0 xstack1 ->
      resolve_effect in1 out1 xstack1 xstack' ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left, false) ->
      step
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := ergs_set ergs_left xstack';
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
    forall flags mod_sf contracts mem_pages xstack0 xstack1 context_u128 dest
      regs cond word jump_dest ergs_left,

      cond_activated cond flags  ->

      let ins := OpJump dest in
      fetch_instr regs xstack0 mem_pages
                  {|
                    ins_spec := ins;
                    ins_mods := mk_cmod NoSwap mod_sf;
                    ins_cond := cond
                  |} ->

      resolve_effect__in dest xstack0 xstack1 ->

      resolve_fetch_word regs xstack1 mem_pages dest word ->
      extract_code_address word jump_dest ->

      ergs_remaining xstack1 - base_cost ins = (ergs_left, false) ->
      step
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := ergs_set ergs_left (pc_set jump_dest xstack1);
          gs_context_u128 := context_u128;
        |}
(** -----
<<
## Add
TODO
>>
 *)
  | step_Add:
    forall flags0 mod_swap mod_sf contracts mem_pages mem_pages' xstack0 xstack1 xstack' context_u128 in1 in2 out1 regs regs' cond op1 op2 op1' op2' result new_OF ergs_left,

      cond_activated cond flags0  ->

      let ins := OpAdd in1 in2 out1 in
      fetch_instr regs xstack0 mem_pages
                  {|
                    ins_spec := ins;
                    ins_mods := mk_cmod mod_swap mod_sf;
                    ins_cond := cond
                  |} ->

      resolve_effect in1 out1 xstack0 xstack1 ->

      resolve_fetch_word regs xstack1 mem_pages in1 op1 ->
      resolve_fetch_word regs xstack1 mem_pages in2 op2 ->

      apply_swap mod_swap op1 op2 = (op1', op2') ->
      op1' + op2' = (result, new_OF) ->


      resolve_store regs xstack1 mem_pages out1 (IntValue result) (regs', mem_pages') ->
      update_pc_regular xstack1 xstack' ->

      ergs_remaining xstack' - base_cost ins = (ergs_left, false) ->

      let new_OF_LT := OF_LT_of_bool new_OF in
      let new_EQ := EQ_of_bool (result == zero256) in
      let new_GT := GT_of_bool ( (negb new_EQ) && (negb new_OF_LT) ) in
      let flags1 := mk_fs new_OF_LT new_EQ new_GT in
      step
        {|
          gs_flags        := flags0;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := apply_set_flags mod_sf flags0 flags1;
          gs_regs := regs';
          gs_mem_pages := mem_pages';
          gs_contracts := contracts;
          gs_callstack := ergs_set ergs_left xstack';
          gs_context_u128 := context_u128;
        |}
(** -----
<<
## Sub
TODO
>>
*)
  | step_Sub:
    forall flags0 mod_swap mod_sf contracts mem_pages mem_pages' xstack0 xstack1 xstack' context_u128 in1 in2 out1 regs regs' cond op1 op2 op1' op2' result new_OF ergs_left,

      cond_activated cond flags0  ->

      let ins := OpSub in1 in2 out1 in
      fetch_instr regs xstack0 mem_pages
                  {|
                    ins_spec := ins;
                    ins_mods := mk_cmod mod_swap mod_sf;
                    ins_cond := cond
                  |} ->

      resolve_effect in1 out1 xstack0 xstack1 ->

      resolve_fetch_word regs xstack1 mem_pages in1 op1 ->
      resolve_fetch_word regs xstack1 mem_pages in2 op2 ->

      apply_swap mod_swap op1 op2 = (op1', op2') ->
      op1' - op2' = (result, new_OF) ->


      resolve_store regs xstack1 mem_pages out1 (IntValue result) (regs', mem_pages') ->
      update_pc_regular xstack1 xstack' ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left, false) ->
      let new_OF_LT := OF_LT_of_bool new_OF in
      let new_EQ := EQ_of_bool (result == zero256) in
      let new_GT := GT_of_bool ( (negb new_EQ) && (negb new_OF_LT) ) in
      let flags1 := mk_fs new_OF_LT new_EQ new_GT in
      step
        {|
          gs_flags := flags0;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := apply_set_flags mod_sf flags0 flags1;
          gs_regs := regs';
          gs_mem_pages := mem_pages';
          gs_contracts := contracts;
          gs_callstack := ergs_set ergs_left xstack';
          gs_context_u128 := context_u128;
        |}
(** -----
<<
## Near call

TODO
>>
*)
(*
        let remaining_ergs = current_callstack_entry.ergs_remaining;
        let (passed_ergs, remaining_ergs_for_this_context) = 
            let (remaining_for_this_context, uf) =
                remaining_ergs.overflowing_sub(near_call_abi.ergs_passed);
            if uf {
            } else {
                (near_call_abi.ergs_passed, remaining_for_this_context)
            }
    *)
  | step_NearCall_pass_some_ergs:
    forall flags mods contracts mem_pages xstack0 xstack1 context_u128 sp regs cond abi_params_op abi_params_value call_addr expt_handler ergs_left ergs_left_ins_paid,

      cond_activated cond flags  ->

      let ins := OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler) in
      fetch_instr regs xstack0 mem_pages
                  {|
                    ins_spec := ins;
                    ins_mods := mods;
                    ins_cond := cond
                  |} ->

      resolve_fetch_word regs xstack0 mem_pages abi_params_op abi_params_value ->

      fetch_sp xstack0 sp -> (* sp is copied as is*)
      update_pc_regular xstack0 xstack1 ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left_ins_paid, false) ->
      let passed_ergs := (NearCall.ABI.(decode) abi_params_value).(NearCall.nca_get_ergs_passed) in
      passed_ergs <> zero32 ->

      (ergs_left, false) = ergs_left_ins_paid - passed_ergs  ->

      let new_frame := mk_cf expt_handler sp call_addr passed_ergs in
      step
        {|
          gs_flags := flags;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags_clear;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := InternalCall new_frame (ergs_set ergs_left xstack1);
          gs_context_u128 := context_u128;
        |}

  | step_NearCall_underflow_pass_all_ergs:
    forall flags mods contracts mem_pages xstack0 xstack1 context_u128 sp regs cond abi_params_op abi_params_value call_addr expt_handler remaining ergs_left,

      cond_activated cond flags  ->

      let ins := OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler) in
      fetch_instr regs xstack0 mem_pages
                  {|
                    ins_spec := ins;
                    ins_mods := mods;
                    ins_cond := cond
                  |} ->

      resolve_fetch_word regs xstack0 mem_pages abi_params_op abi_params_value ->

      fetch_sp xstack0 sp -> (* sp is copied as is*)
      update_pc_regular xstack0 xstack1 ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left, false) ->

      let passed_ergs := (NearCall.ABI.(decode) abi_params_value).(NearCall.nca_get_ergs_passed) in
      passed_ergs <> zero32 ->
      (remaining, true) = ergs_remaining xstack0 - passed_ergs ->

      let new_frame := mk_cf expt_handler sp call_addr remaining in
      step
        {|
          gs_flags := flags;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags_clear;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := InternalCall new_frame (ergs_zero xstack1);
          gs_context_u128 := context_u128;
        |}

  | step_NearCall_pass_all_ergs:
    forall flags mods contracts mem_pages xstack0 xstack1 context_u128 sp regs cond abi_params_op abi_params_value call_addr expt_handler ergs_left,

      cond_activated cond flags  ->

      let ins := OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler) in
      fetch_instr regs xstack0 mem_pages
                  {|
                    ins_spec := ins;
                    ins_mods := mods;
                    ins_cond := cond
                  |} ->

      resolve_fetch_word regs xstack0 mem_pages abi_params_op abi_params_value ->

      fetch_sp xstack0 sp -> (* sp is copied as is*)
      update_pc_regular xstack0 xstack1 ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left, false) ->
      (NearCall.ABI.(decode) abi_params_value).(NearCall.nca_get_ergs_passed) = zero32 ->

      let new_frame := mk_cf expt_handler sp call_addr ergs_left in
      step
        {|
          gs_flags := flags;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags_clear;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := InternalCall new_frame (ergs_zero xstack1);
          gs_context_u128 := context_u128;
        |}
 
(** -----
<<
## BinOp (bitwise operations)

TODO
>>
*)

  | step_BinOp:
    forall flags0 mod_swap mod_sf contracts mem_pages mem_pages' xstack0 xstack1 xstack' context_u128 in1 in2 out1 regs regs' cond op1 op2 op1' op2' result opmod ergs_left,
      cond_activated cond flags0  ->

      fetch_instr regs xstack0 mem_pages
                  {|
                    ins_spec := OpBinOp in1 in2 out1 opmod;
                    ins_mods := mk_cmod mod_swap mod_sf;
                    ins_cond := cond
                  |} ->

      resolve_effect in1 out1 xstack0 xstack1 ->

      resolve_fetch_word regs xstack1 mem_pages in1 op1 ->
      resolve_fetch_word regs xstack1 mem_pages in2 op2 ->

      apply_swap mod_swap op1 op2 = (op1', op2') ->
      binop_func opmod op1' op2' = result ->

      resolve_store regs xstack1 mem_pages out1 (IntValue result) (regs', mem_pages') ->
      update_pc_regular xstack1 xstack' ->

      ergs_remaining xstack0 - base_cost (OpBinOp in1 in2 out1 opmod) = (ergs_left, false) ->
      let new_EQ := EQ_of_bool (result == zero256) in
      let flags' := apply_set_flags mod_sf flags0 (mk_fs Clear_OF_LT new_EQ Clear_GT) in
      step
        {|
          gs_flags := flags0;
          gs_regs := regs;
          gs_mem_pages := mem_pages;
          gs_contracts := contracts;
          gs_callstack := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags := flags';
          gs_regs := regs';
          gs_mem_pages := mem_pages';
          gs_contracts := contracts;
          gs_callstack := ergs_set ergs_left xstack';
          gs_context_u128 := context_u128;
        |}
(** -----
<<
## Returns

TODO
>>
 *)
  | step_RetLocalOk_nolabel:
    forall flags mods contracts mem_pages cf caller_stack caller_stack' context_u128 regs cond ignored ergs_left,

      cond_activated cond flags  ->

      let ins := OpRetOK ignored None in
      let xstack0 := InternalCall cf caller_stack in
      fetch_instr regs xstack0 mem_pages (Ins ins mods cond) ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left, false) ->
      ergs_reimburse ergs_left caller_stack caller_stack' ->
      step
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := InternalCall cf caller_stack;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := flags_clear;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := caller_stack';
          gs_context_u128 := context_u128;
        |}

  | step_RetLocalOk_label:
    forall flags contracts mem_pages cf caller_stack caller_stack' context_u128 regs cond mods ignored label ergs_left,

      cond_activated cond flags  ->

      let xstack0 := InternalCall cf caller_stack in
      let ins := OpRetOK ignored (Some label) in
      fetch_op regs xstack0 mem_pages ins mods cond ->

      ergs_remaining xstack0  - base_cost ins = (ergs_left, false) ->
      ergs_reimburse ergs_left caller_stack caller_stack' ->

      step
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := InternalCall cf caller_stack;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := flags_clear;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := pc_set label caller_stack';
          gs_context_u128 := context_u128;
        |}

  | step_RetLocalRevert_nolabel:
    forall flags mods contracts mem_pages caller_stack caller_stack' context_u128 regs cond ignored except_handler sp pc ergs ergs_left,

      cond_activated cond flags  ->

      let xstack0 := InternalCall (mk_cf except_handler sp pc ergs) caller_stack in
      let ins := OpRetRevert ignored None in
      fetch_op regs xstack0 mem_pages ins mods cond ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left, false) ->
      ergs_reimburse ergs_left caller_stack caller_stack' ->

      step
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := flags_clear;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := pc_set except_handler caller_stack';
          gs_context_u128 := context_u128;
        |}

  | step_RetLocalRevert_label:
    forall flags contracts mem_pages cf caller_stack caller_stack' context_u128 regs cond mods ignored label ergs_left,

      cond_activated cond flags  ->
      let xstack0 := InternalCall cf caller_stack in
      let ins := OpRetRevert ignored (Some label) in
      fetch_op regs xstack0 mem_pages ins mods cond ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left, false) ->
      ergs_reimburse ergs_left caller_stack caller_stack' ->

      step
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := flags_clear;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := (pc_set label caller_stack');
          gs_context_u128 := context_u128;
        |}

  | step_RetLocalPanic_nolabel:
    forall flags mods contracts mem_pages caller_stack caller_stack' context_u128 regs cond except_handler sp pc ergs_remaining ergs_left,

      cond_activated cond flags  ->

      let ins := OpRetPanic None in
      let xstack0 := InternalCall (mk_cf except_handler sp pc ergs_remaining) caller_stack in
        fetch_op regs xstack0 mem_pages ins mods cond ->

      ergs_remaining - base_cost ins = (ergs_left, false) ->
      ergs_reimburse ergs_left caller_stack caller_stack' ->

      step
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := xstack0;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := mk_fs Set_OF_LT Clear_EQ Clear_GT;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := pc_set except_handler caller_stack';
          gs_context_u128 := context_u128;
        |}

  | step_RetLocalPanic_label:
    forall flags contracts mem_pages cf caller_stack caller_stack' context_u128 regs cond mods label ergs_left,

      cond_activated cond flags  ->

      let xstack0 := InternalCall cf caller_stack in
      let ins := OpRetPanic (Some label) in
      fetch_op regs xstack0 mem_pages ins mods cond ->

      ergs_remaining xstack0 - base_cost ins = (ergs_left, false) ->
      ergs_reimburse ergs_left caller_stack caller_stack' ->

      step
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := InternalCall cf caller_stack;
          gs_context_u128 := context_u128;
        |}
        {|
          gs_flags        := mk_fs Set_OF_LT Clear_EQ Clear_GT;
          gs_regs         := regs;
          gs_mem_pages    := mem_pages;
          gs_contracts    := contracts;
          gs_callstack    := pc_set label caller_stack';
          gs_context_u128 := context_u128;
        |}
(* TODO returns from far calls *)
  .

End Execution.
