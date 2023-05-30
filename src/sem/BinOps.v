From RecordUpdate Require Import RecordSet.
Require  sem.SemanticCommon.

Import Bool ZArith Common Condition Instruction ExecutionStack Memory MemoryOps State ZMod
  ZBits Arg Arg.Coercions RecordSetNotations SemanticCommon.

Inductive binop_effect: execution_stack -> regs_state -> pages -> flags_state ->
                        in_any -> in_any -> out_any ->
                        mod_swap -> mod_set_flags ->
                        (word_type -> word_type -> (word_type * flags_state)) ->
                        (execution_stack * regs_state * pages * flags_state) -> Prop :=
| be_apply:
  forall f ef0 ef1 ef' regs regs' mm mm' (in1 in2: in_any) (out: out_any) loc1 loc2
    op1 op2 op1' op2' swap set_flags out_loc result flags_candidate flags0 new_flags,
    resolve ef0 regs in1 loc1 ->
    resolve_effect__in in1 ef0 ef1 ->
    resolve ef1 regs in2 loc2 ->
    resolve ef1 regs out out_loc ->
    resolve_effect__out out ef1 ef' ->
    fetch_loc regs ef' mm loc1 (FetchPV (IntValue op1)) ->
    fetch_loc regs ef' mm loc2 (FetchPV (IntValue op2)) ->
    apply_swap swap op1 op2 = (op1', op2') ->
    f op1' op2' = (result, flags_candidate) ->
    store_loc regs ef' mm (IntValue result) out_loc (regs', mm') ->
    new_flags = apply_set_flags set_flags flags0 flags_candidate ->
    binop_effect ef0 regs mm flags0 in1 in2 out swap set_flags f (ef', regs', mm', new_flags).

Inductive binop_state_effect: in_any -> in_any -> out_any -> mod_swap -> mod_set_flags ->
                      (word_type -> word_type -> (word_type * flags_state)) ->
                      smallstep :=
| be_apply_step:
  forall f xstack new_xstack context_u128 regs new_regs pages new_pages depot (in1 in2: in_any) (out: out_any) swap set_flags flags new_flags codes,
    let gs := {|
          gs_flags        := flags;
          gs_callstack    := xstack;
          gs_regs         := regs;
          gs_context_u128 := context_u128;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_contracts    := codes;
          |}  in
    binop_effect xstack regs pages flags in1 in2 out swap set_flags f (new_xstack, new_regs, new_pages, new_flags) ->
    binop_state_effect
      in1 in2 out swap set_flags f gs
      {|
        gs_flags        := new_flags;
        gs_callstack    := new_xstack;
        gs_regs         := new_regs;
        gs_context_u128 := context_u128;
        gs_pages        := new_pages;
        gs_depot        := depot;
        gs_contracts    := codes;
      |}
.

Inductive step: instruction -> smallstep :=
(**
<<
## Add
Unsigned addition of two numbers.
>>
*)
| step_Add:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_state_effect in1 in2 out mod_swap mod_sf
      (fun x y =>
         let (result, NEW_OF) := x + y in
         let NEW_EQ := EQ_of_bool (result == zero256) in
         let NEW_GT := GT_of_bool (negb NEW_EQ && negb NEW_OF) in
         (result, mk_fs (OF_LT_of_bool NEW_OF) NEW_EQ NEW_GT))
      gs gs' ->

    step (OpAdd in1 in2 out mod_swap mod_sf) gs gs'
(**
<<
## Sub
Unsigned subtraction of two numbers.
>>
 *)

| step_Sub:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_state_effect in1 in2 out mod_swap mod_sf
      (fun x y =>
         let (result, NEW_OF) := x - y in
         let NEW_EQ := EQ_of_bool (result == zero256) in
         let NEW_GT := GT_of_bool (negb NEW_EQ && negb NEW_OF) in
         (result, mk_fs (OF_LT_of_bool NEW_OF) NEW_EQ NEW_GT))
      gs gs' ->

    step (OpSub in1 in2 out mod_swap mod_sf) gs gs'
(**
<<
## And
Bitwise AND of two numbers.
>>
 *)

| step_And:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_state_effect in1 in2 out mod_swap mod_sf
      (fun x y => let result := bitwise_and _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
      gs gs' ->

    step (OpAnd in1 in2 out mod_swap mod_sf) gs gs'
(**
<<
## Or
Bitwise OR of two numbers.
>>
 *)
| step_Or:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_state_effect in1 in2 out mod_swap mod_sf
      (fun x y => let result := bitwise_or _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
      gs gs' ->

    step (OpOr in1 in2 out mod_swap mod_sf) gs gs'

(**
<<
## Xor
Bitwise XOR of two numbers.
>>
 *)
| step_Xor:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_state_effect in1 in2 out mod_swap mod_sf
      (fun x y => let result := bitwise_xor _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
      gs gs' ->

    step (OpXor in1 in2 out mod_swap mod_sf) gs gs'
.
