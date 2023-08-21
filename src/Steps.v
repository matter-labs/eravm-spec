From RecordUpdate Require Import RecordSet.

Require
  Flags
    isa.CoreSet
    KernelMode
    State.
Import
  Flags
    isa.CoreSet
    KernelMode
    RecordSetNotations
    State.

(** A type of a small step relation, in style of structural operational semantics. *)
Definition smallstep := state -> state -> Prop .
Definition tsmallstep := transient_state -> transient_state -> Prop.
Definition flags_tsmallstep := flags_state -> flags_state -> Prop.
Definition callstack_smallstep := callstack -> callstack -> Prop.

(** Relations [%step_transient_only] and [%step_transient] define the type of
small steps only affecting [%gs_transient] part. *)
Inductive step_transient_only (xs1 xs2:transient_state) : smallstep :=
| stransient_oapply:
  forall gs,
    step_transient_only xs1 xs2 {|
                          gs_transient       := xs1;
                          gs_global       := gs;
                        |}
                        {|
                          gs_transient       := xs2;
                          gs_global       := gs;
                        |}.

Inductive step_transient (S: transient_state -> transient_state -> Prop) : smallstep :=
| stransient_apply:
  forall xs1 xs2 s1 s2 ,
    S xs1 xs2 ->
    step_transient_only xs1 xs2 s1 s2->
    step_transient S s1 s2.

(** Relations [%tstep_flags] and [%step_transient_callstack] help defining
smallstep relations where only flags or callstack are changing. *)
Definition tstep_flags {descr:CoreSet.descr} (P: @instruction descr -> flags_tsmallstep): @instruction descr -> tsmallstep :=
  fun i xs xs' => forall f2, P i (gs_flags xs) f2 -> xs' = xs <| gs_flags := f2 |>.

(** Relations [%step_transient_callstack] and  help defining
smallstep relations where only callstack is changing. *)
Inductive step_transient_callstack (S: callstack -> callstack -> Prop) : transient_state -> transient_state -> Prop :=
| scs_apply:
  forall flags regs pages ctx cs1 cs2 xs1 xs2 status,
    S cs1 cs1 ->
    xs1 = {|
            gs_callstack    := cs1;

            gs_flags        := flags;
            gs_regs         := regs;
            gs_pages        := pages;
            gs_context_u128 := ctx;
            gs_status       := status;
          |} ->
    xs2 = {|
            gs_callstack    := cs2;


            gs_flags        := flags;
            gs_regs         := regs;
            gs_pages        := pages;
            gs_context_u128 := ctx;
            gs_status       := status;
          |} ->

    step_transient_callstack S xs1 xs2.

Inductive step_callstack (S: callstack -> callstack -> Prop) : smallstep :=
| sc_apply: forall xs1 xs2 s1 s2,
    step_transient_callstack S xs1 xs1 ->
    step_transient_only xs1 xs2 s1 s2 ->
    step_callstack S s1 s2.
