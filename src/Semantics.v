From RecordUpdate Require Import RecordSet.
Require VMPanic StaticMode isa.AssemblyToCore sem.SemanticCommon.

(* begin hide *)
Import ZArith Common GPR Predication Ergs CallStack Memory MemoryOps Assembly CoreSet State ZMod
  RecordSetNotations SemanticCommon KernelMode StaticMode VMPanic Binding Steps.
Import List ListNotations AssemblyToCore.Coercions.
Require Import
  sem.Add
  sem.And
  sem.Context
  sem.Div
  sem.FarRet
  sem.FarRevert
  sem.Farcall
  sem.Jump
  sem.Load
  sem.LoadInc
  sem.LoadPtr
  sem.LoadPtrInc
  sem.SpAdd
  sem.SpSub
  sem.Mul
  sem.NearCall
  sem.NearPanicTo
  sem.NearRet
  sem.NearRetTo
  sem.NearRevert
  sem.NearRevertTo
  sem.OpEvent
  sem.Or
  sem.Panic
  sem.PrecompileCall
  sem.PtrAdd
  sem.PtrPack
  sem.PtrShrink
  sem.PtrSub
  sem.Rol
  sem.Ror
  sem.SLoad
  sem.SStore
  sem.Shl
  sem.Shr
  sem.Store
  sem.StoreInc
  sem.Sub
  sem.ToL1
  sem.Xor
.
(* end hide *)

Section VMParameters.
  Local Open Scope ZMod_scope.
  Local Coercion int_val : int_mod >-> Z.

  Definition VM_INITIAL_FRAME_ERGS: nat := Z.to_nat (unsigned_max ergs_bits).
  Context (CALL_LIKE_ERGS_COST  := Z.to_nat CALL_LIKE_ERGS_COST).
  Definition VM_MAX_STACK_DEPTH: nat := VM_INITIAL_FRAME_ERGS / CALL_LIKE_ERGS_COST + 80.
End VMParameters.

Section SmallStep.
  Local Open Scope ZMod_scope.

  Context (ins := @instruction bound).

  Inductive update_pc_regular : callstack -> callstack -> Prop :=
  | fp_update:
    forall pc' ef,
      let pc := pc_get ef in
      uinc_overflow _ pc = (pc',false) ->
      let ef' := pc_set pc' ef in
      update_pc_regular ef ef'.

  (** Every instruction is either executed, skipped, or triggers panic
  instantly. Panic can also be triggered later during the execution. *)
  Inductive action: Type := Execute | Skip | Panic : reason -> action.

  (** After the instruction is selected, panic is immediately triggered:

- on call stack overflow;
- if the [%base_cost] of instruction is unaffordable;
- if the instruction is not allowed in kernel mode, and VM is in kernel mode;
- if the instruction is not allowed in static mode, and VM is in static mode.
   *)
  Definition chose_action (s:transient_state) (i:@predicated asm_instruction) : action :=
    if stack_overflow VM_MAX_STACK_DEPTH (gs_callstack s) then
      Panic CallStackOverflow
    else if negb (check_requires_kernel i.(ins_spec _) (in_kernel_mode (gs_callstack s))) then
           Panic NotInKernelMode
         else if negb (check_forbidden_static i.(ins_spec _) (active_extframe (gs_callstack s)).(ecf_is_static)) then
                Panic ForbiddenInStaticMode
              else if negb (predicate_holds i.(ins_cond _) (gs_flags s)) then
                     Skip
                   else Execute.

  (** The definition [%smallsteps] gathers the references to all the small step
  predicates for various [%asm_instruction]s. *)
  Definition smallsteps : list (@instruction bound -> smallstep) :=
  [
  fun i => step_transient (tstep_flags     step_add          i);
  fun i => step_transient (tstep_flags     step_sub          i);
  fun i => step_transient (tstep_flags     step_and          i);
                                        step_context;
  fun i => step_transient (tstep_flags     step_mul          i);
  fun i => step_transient (tstep_flags     step_div          i);
  fun i => step_transient (                step_farret       i);
                                        step_farrevert      ;
                                        step_farcall        ;
                                        step_jump;
  fun i => step_transient (                step_load         i);
  fun i => step_transient (                step_load_inc     i);
  fun i => step_transient (                step_load_ptr     i);
  fun i => step_transient (                step_load_ptr_inc i);
  fun i => step_transient (tstep_flags     step_mul          i);
  fun i => step_callstack (                step_sp_add       i);
  fun i => step_callstack (                step_sp_sub       i);
                                        step_nearcall       ;
                                        step_panicto        ;
  fun i => step_transient (                step_nearret      i);
  fun i => step_transient (                step_nearretto    i);
                                        step_nearrevert     ;
                                        step_nearrevertto   ;
                                        step_event          ;
  fun i => step_transient (tstep_flags     step_or           i);
                                        step_oppanic        ;
                                        step_precompile     ;
                                        step_ptradd         ;
                                        step_ptrsub         ;
                                        step_ptrshrink      ;
                                        step_ptrpack        ;
  fun i => step_transient (tstep_flags     step_rol          i);
  fun i => step_transient (tstep_flags     step_ror          i);
                                        step_sload          ;
                                        step_sstore         ;
  fun i => step_transient (tstep_flags     step_shl          i);
  fun i => step_transient (tstep_flags     step_shr          i);
  fun i => step_transient (                step_store        i);
  fun i => step_transient (                step_storeinc     i);
                                        step_tol1           ;
  fun i => step_transient (tstep_flags     step_xor          i)

  ].

  Inductive dispatch: @instruction bound -> smallstep :=
  | dispatch_apply: forall s1 s2 ins S,
      In S smallsteps ->
      S ins s1 s2 ->
      dispatch ins s1 s2.

  Generalizable Variables cs.

  Inductive execute_action: action -> @instruction decoded -> smallstep :=
  | ea_execute:
    `(forall instr gs instr_bound new_s xs0 xs1,
          cs0 = gs_callstack xs0 ->

          update_pc_regular cs0 cs1 ->
          pay (ergs_of (base_cost instr)) cs1 cs2 ->
          bind_operands (xs0 <| gs_callstack := cs2 |>) xs1 instr instr_bound ->
          let s1 := mk_state xs1 gs in
          dispatch instr_bound s1 new_s ->
          execute_action Execute instr (mk_state xs0 gs) new_s
      )
  | ea_skip:
    `(forall instr gs xs0 xs1,
          cs0 = gs_callstack xs0 ->

          update_pc_regular cs0 cs1 ->
          pay (ergs_of (base_cost instr)) cs1 cs2 ->
          let new_s := mk_state xs1 gs in
          execute_action Skip instr (mk_state xs0 gs) new_s
      )
  | ea_panic:
    forall reason s new_s instr,
      step_panic reason s new_s ->
      execute_action (Panic reason) instr s new_s
  .

  Generalizable No Variables.


  Definition fetch_predicated_instruction (s: transient_state) ins :=
    @fetch_instr _ instruction_invalid _ (gs_regs s) (gs_callstack s) (gs_pages s)
      (@FetchIns (predicated asm_instruction) ins).



 (** [%step] is the main predicate defining a VM transition in a small step
 structural operational style. *)
  Inductive step: smallstep :=
  | step_correct:
    forall (s new_s : state) cond
      (instr:asm_instruction)
      (ins_bound:@instruction bound),

      fetch_predicated_instruction  s (Ins _ instr cond) ->
      execute_action (chose_action s (Ins _ instr cond)) instr s new_s ->
      step s new_s.
End SmallStep.
