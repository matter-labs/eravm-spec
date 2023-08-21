Require Addressing CallStack Common GPR Flags isa.CoreSet State Steps VMPanic.
Import Addressing CallStack Common GPR Flags isa.CoreSet State Steps VMPanic.

Section StepPanic.
  (** # Handling panics

EraVM handles the panic situation as follows:

- return from the current function signaling an error;
- execute exception handler;
- burn all ergs in current frame;
- set OF flag;
- restore depot and event queues to the state before external call (see [%gs_revertable]).
- when returning from a far call, return no data.

## Case 1: `panic` from near call

1. Perform a [%rollback].
2. Drop current frame with its ergs.
3. Set PC to the exception handler of a dropped frame.
4. Clear flags, and set OF.
   *)
  Inductive step_panic reason: smallstep :=
  | step_PanicLocal_nolabel:
    forall flags pages cf caller_stack regs gs gs' __,
      let handler := active_exception_handler (InternalCall cf caller_stack) in
      rollback (cf_saved_checkpoint cf) gs gs' ->
      step_panic reason
                 {|
                   gs_transient:= {|
                                   gs_flags        := flags;
                                   gs_callstack    := InternalCall cf caller_stack;
                                   gs_regs         := regs;
                                   gs_context_u128 := __;
                                   gs_status       := Panic reason;


                                   gs_pages        := pages;
                                 |};

                   gs_global       := gs;
                 |}
                 {|
                   gs_transient:= {|
                                   gs_flags        := set_overflow flags_clear;
                                   gs_regs         := regs_state_zero;
                                   gs_callstack    := pc_set cf.(cf_exception_handler_location) caller_stack;
                                   gs_context_u128 := zero128;
                                   gs_status       := NoPanic;

                                   gs_pages        := pages;
                                 |};

                   gs_global       := gs'
                 |}
  (**
## Case 2: `panic` from external call

1. Perform a [%rollback].
2. Drop current frame and its ergs
3. Clear flags and set OF.
4. Clear context register.
5. Set PC to the exception handler address of a dropped frame.
6. All storages are reverted to the state prior to the current contract call.
7. Put an encoded zero-pointer into `R1` and tag `R1` as a pointer.

   All other registers are zeroed. Registers `R2`, `R3` and `R4` are reserved
   and may gain a special meaning in newer versions of EraVM.
   *)
  | step_PanicExt:
    forall flags pages cf caller_stack __ regs gs gs',
      let cs0 := ExternalCall cf (Some caller_stack) in
      rollback (cf_saved_checkpoint cf) gs gs' ->
      step_panic reason
                 {|
                   gs_transient := {|
                                    gs_flags        := flags;
                                    gs_callstack    := cs0;
                                    gs_regs         := regs;
                                    gs_context_u128 := __;
                                    gs_status       := Panic reason;


                                    gs_pages        := pages;
                                  |};

                   gs_global       := gs;
                 |}
                 {|
                   gs_transient := {|
                                    gs_flags        := set_overflow flags_clear;
                                    gs_regs         := regs_state_zero;
                                    gs_callstack    := pc_set (active_exception_handler cs0) caller_stack;
                                    gs_context_u128 := zero128;
                                    gs_status       := NoPanic;

                                    gs_pages        := pages;
                                  |};

                   gs_global       := gs'
                 |}
  .
End StepPanic.
