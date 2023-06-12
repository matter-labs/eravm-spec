From RecordUpdate Require Import RecordSet.
Require sem.Ret sem.Farcall sem.BinOps sem.ModSP sem.Jump sem.Ptr sem.UMA sem.Context sem.Div sem.Mul sem.NearCall.

Import Bool ZArith Common CodeStorage Condition Ergs ExecutionStack MemoryBase Memory MemoryOps Instruction State ZMod
  ZBits SemanticCommon RecordSetNotations.

Inductive step_ins: instruction -> smallstep :=
(**
## NoOp

Performs no operations.
*)
| step_ins_noop: forall gs, step_ins OpNoOp gs gs
| step_ins_jump: forall ins gs gs', Jump.step ins gs gs' -> step_ins ins gs gs'
| step_ins_modsp: forall ins gs gs', ModSP.step ins gs gs' -> step_ins ins gs gs'
| step_ins_farcall: forall ins gs gs', Farcall.step ins gs gs' -> step_ins ins gs gs'
| step_ins_ret: forall ins gs gs', Ret.step_ret ins gs gs' -> step_ins ins gs gs'
| step_ins_revert: forall ins gs gs', Ret.step_revert ins gs gs' -> step_ins ins gs gs'
| step_ins_panic: forall ins gs gs', Ret.step_panic ins gs gs' -> step_ins ins gs gs'
| step_ins_binop: forall ins gs gs', BinOps.step ins gs gs' -> step_ins ins gs gs'
| step_ins_ptr: forall ins gs gs', Ptr.step ins gs gs' -> step_ins ins gs gs'
| step_ins_uma: forall ins gs gs', UMA.step ins gs gs' -> step_ins ins gs gs'
| step_ins_nearcall: forall ins gs gs', NearCall.step ins gs gs' -> step_ins ins gs gs'
| step_ins_context: forall ins gs gs', Context.step ins gs gs' -> step_ins ins gs gs'
| step_ins_mul: forall ins gs gs', Mul.step ins gs gs' -> step_ins ins gs gs'
| step_ins_div: forall ins gs gs', Div.step ins gs gs' -> step_ins ins gs gs'
.


Inductive step: smallstep := 
   | step_correct:
    forall gs flags  pages xstack0 xstack1 new_xstack ins context_u128 regs cond new_gs,
      let gs0 := {|
          gs_callstack    := xstack0;

          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          
          gs_context_u128 := context_u128;
          gs_global       := gs;
          |} in
      let gs1 := {|
          gs_callstack    := new_xstack;

          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          
          gs_context_u128 := context_u128;
          gs_global       := gs;
          |} in
      cond_holds cond flags = true ->

      stack_overflow xstack0 = false ->
      check_requires_kernel ins (is_kernel xstack0) = true ->
      check_allowed_static_ctx ins (topmost_extframe xstack0).(ecf_is_static) = true ->
      fetch_instr regs xstack0 pages (Ins ins cond) ->

      update_pc_regular xstack0 xstack1 ->
      pay (ergs_of (base_cost ins)) xstack1 new_xstack ->
      step_ins ins gs1 new_gs ->
      step gs0 new_gs
 | step_requires_kernel:
    forall cond gs flags  pages xstack0 ins context_u128 regs new_gs,
      let gs0 := {|
          gs_callstack    := xstack0;

          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          
          gs_context_u128 := context_u128;
          gs_global       := gs;
          |} in
      stack_overflow xstack0 = false ->
      fetch_instr regs xstack0 pages (Ins ins cond) ->
      check_requires_kernel ins (is_kernel xstack0) = false ->
      
      step_ins (OpPanic None) gs0 new_gs->
      step gs0 new_gs
| step_incompatible_static:
    forall cond gs flags  pages xstack0 ins context_u128 regs new_gs,
      let gs0 := {|
          gs_callstack    := xstack0;

          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          
          gs_context_u128 := context_u128;
          gs_global       := gs;
          |} in

      check_allowed_static_ctx ins (topmost_extframe xstack0).(ecf_is_static) = false ->
      stack_overflow xstack0 = false ->
      fetch_instr regs xstack0 pages (Ins ins cond) ->
      check_requires_kernel ins (is_kernel xstack0) = true ->
      
      step_ins (OpPanic None) gs0 new_gs->
      step gs0 new_gs

| step_skip_cond:
    forall gs flags  pages xstack0 xstack1 new_xstack ins context_u128 regs cond new_gs,
      let gs0 := {|
          gs_callstack    := xstack0;

          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          
          gs_context_u128 := context_u128;
          gs_global       := gs;
          |} in
      let gs1 := {|
          gs_callstack    := new_xstack;

          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          
          gs_context_u128 := context_u128;
          gs_global       := gs;
          |} in
      (* Checks have passed *)
      cond_holds cond flags = false ->
      stack_overflow xstack0 = false ->
      check_requires_kernel ins (is_kernel xstack0) = true ->
      check_allowed_static_ctx ins (topmost_extframe xstack0).(ecf_is_static) = true ->

      fetch_instr regs xstack0 pages (Ins ins cond) ->

      update_pc_regular xstack0 xstack1 ->
      (* Still pay the price of the fetched instruction *)
      pay (ergs_of (base_cost ins)) xstack1 new_xstack ->
      step_ins OpNoOp gs1 new_gs ->
      step gs0 new_gs

 | step_stack_overflow:
   forall gs flags  pages xstack0 context_u128 regs new_gs,
      let gs0 := {|
          gs_callstack    := xstack0;

          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          
          gs_context_u128 := context_u128;
          gs_global       := gs;
          |} in
      stack_overflow xstack0 = true ->
      step_ins (OpPanic None) gs0 new_gs->
      step gs0 new_gs.
 
