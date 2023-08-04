Require Addressing CallStack Common GPR Flags isa.CoreSet State Steps.
Import Addressing CallStack Common GPR Flags isa.CoreSet State Steps.


Inductive reason:=
| NotEnoughErgs
| NotInKernelMode
| ForbiddenInStaticMode
| InvariantViolation
| CallStackOverflow
| InvalidInstruction
| ExpectedPointerInInstruction {descr} (op:@instruction descr)
| TriggeredExplicitly
.

Inductive step_panic (why:reason) : smallstep :=
| step_PanicLocal_nolabel:
    forall flags pages cf caller_stack regs gs gs' __,
      let handler := active_exception_handler (InternalCall cf caller_stack) in
      roll_back (cf_saved_checkpoint cf) gs gs' ->
      step_panic why
                 {|
            gs_transient:= {|
                          gs_flags        := flags;
                          gs_callstack    := InternalCall cf caller_stack;
                          gs_regs         := regs;
                          gs_context_u128 := __;


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

                          gs_pages        := pages;
                          |};



          gs_global       := gs'
          |}

| step_PanicExt:
  forall flags pages cf caller_stack __ regs (arg:in_reg) gs gs',
    let cs0 := ExternalCall cf (Some caller_stack) in
    roll_back (cf_saved_checkpoint cf) gs gs' ->
    step_panic why
          {|
            gs_transient := {|
                          gs_flags        := flags;
                          gs_callstack    := cs0;
                          gs_regs         := regs;
                          gs_context_u128 := __;


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

                          gs_pages        := pages;
                          |};



          gs_global       := gs'
          |}
.
