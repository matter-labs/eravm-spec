From RecordUpdate Require Import RecordSet.
Require  sem.SemanticCommon.

Import Addressing Bool ZArith Common Condition Instruction ExecutionStack Memory MemoryOps State ZMod
  ZBits Addressing.Coercions RecordSetNotations SemanticCommon List ListNotations.

Local Coercion u256_of : Z >-> int_mod.

Inductive step: instruction -> smallstep :=

  | step_Div_no_overflow:
    forall gs flags pages xstack context_u128 regs (arg_op1:in_any) (arg_op2:in_reg) (arg_out1:out_any) (arg_out2:out_reg) any_tag1 any_tag2 mod_swap mod_flags (x y:Z) new_regs new_xstack new_pages new_flags quot rem,
      fetch_apply22_swap mod_swap (regs,xstack,pages)
                     arg_op1 arg_op2
                     arg_out1 arg_out2
                     (mk_pv any_tag1 x) (mk_pv any_tag2 y) (IntValue quot, IntValue rem)
                     (new_regs, new_xstack, new_pages) ->
      y <> 0%Z ->
      quot = Z.div x y ->
      rem = Z.rem x y ->

      let new_EQ := quot == zero256 in
      let new_GT := rem == zero256 in 
      new_flags = apply_set_flags mod_flags flags (bflags false new_EQ new_GT) ->
                       
      step (OpDiv arg_op1 arg_op2 arg_out1 arg_out2 mod_swap mod_flags)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_callstack    := xstack;
          gs_pages        := pages;


          gs_context_u128 := context_u128;
          gs_global       := gs;
        |}
        {|
          gs_flags        := new_flags;
          gs_regs         := new_regs;
          gs_callstack    := new_xstack;
          gs_pages        := new_pages;


          gs_context_u128 := context_u128;
          gs_global       := gs;
        |}
  | step_Div_overflow:
    forall gs flags pages xstack context_u128 regs (arg_op1:in_any) (arg_op2:in_reg) (arg_out1:out_any) (arg_out2:out_reg) any_tag1 any_tag2 mod_swap mod_flags (x y:Z) new_regs new_xstack new_pages new_flags,
      fetch_apply22_swap mod_swap (regs,xstack,pages)
                     arg_op1 arg_op2
                     arg_out1 arg_out2
                     (mk_pv any_tag1 x) (mk_pv any_tag2 y) (IntValue 0%Z, IntValue 0%Z)
                     (new_regs, new_xstack, new_pages) ->
      y = 0%Z ->

      new_flags = apply_set_flags mod_flags flags (bflags true false false) ->
                       
      step (OpDiv arg_op1 arg_op2 arg_out1 arg_out2 mod_swap mod_flags)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_callstack    := xstack;
          gs_pages        := pages;


          gs_context_u128 := context_u128;
          gs_global       := gs;
        |}
        {|
          gs_flags        := new_flags;
          gs_regs         := new_regs;
          gs_callstack    := new_xstack;
          gs_pages        := new_pages;


          gs_context_u128 := context_u128;
          gs_global       := gs;
        |}
.
