From RecordUpdate Require Import RecordSet.
Require  sem.SemanticCommon.

Import Addressing Bool ZArith Common Condition Instruction ExecutionStack Memory MemoryOps State ZMod
  ZBits Addressing.Coercions RecordSetNotations SemanticCommon List ListNotations.

Local Coercion u256_of : Z >-> int_mod.

Inductive step: instruction -> smallstep :=

  | step_Mul:
    forall codes flags depot pages xstack context_u128 regs (arg_op1:in_any) (arg_op2:in_reg) (arg_out1:out_any) (arg_out2:out_reg) any_tag1 any_tag2 mod_swap mod_flags (x y prod_hi prod_low:Z) new_regs new_xstack new_pages new_flags,
      fetch_apply22_swap mod_swap (regs,xstack,pages)
                     arg_op1 arg_op2
                     arg_out1 arg_out2
                     (mk_pv any_tag1 x) (mk_pv any_tag2 y) (IntValue prod_hi, IntValue prod_low)
                     (new_regs, new_xstack, new_pages) ->

      extract_digits (x * y) word_bits 2 = [ prod_hi;  prod_low ] -> 

      let new_EQ := prod_low == zero256 in
      let new_OF := prod_hi != zero256 in
      let new_GT := andb (negb new_OF) (negb new_EQ) in 
      new_flags = apply_set_flags mod_flags flags (bflags new_OF new_EQ new_GT) ->
                       
      step (OpMul arg_op1 arg_op2 arg_out1 arg_out2 mod_swap mod_flags)
        {|
          gs_flags        := flags;
          gs_regs         := regs;
          gs_callstack    := xstack;
          gs_pages        := pages;


          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
        {|
          gs_flags        := new_flags;
          gs_regs         := new_regs;
          gs_callstack    := new_xstack;
          gs_pages        := new_pages;


          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
        |}
.
