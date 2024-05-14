Require SemanticCommon.

Import NearCallABI Addressing Common Core Flags CallStack GPR Ergs isa.CoreSet TransientMemory PrimitiveValue State SemanticCommon.
Import ssreflect ssrfun ssrbool eqtype ssreflect.tuple.

Section NearCallDefinition.
  Open Scope ZMod_scope.
  (** {{{!
describe(InstructionDoc(

ins=Instruction("OpNearCall", "call", in1 = In.Reg, in2 = None, imm1 = "dest",imm2="handler"),

syntax_override = [
r"`call abi_reg, callee_address, exception_handler` as a fully expanded form.",

r"""`call abi_reg, callee_address`
  + The assembler expands this variation to
    `call abi_reg, callee_address, DEFAULT_UNWIND_DEST`. Here:
    * `DEFAULT_UNWIND_DEST` is a reserved system label; the linker will resolve it
      to the default exception handler.
""",
r"""`call callee_address` is a simplified form.
  + Assembler expands this variation  to
    `call r0, callee_address, DEFAULT_UNWIND_DEST`, where:
    * `DEFAULT_UNWIND_DEST` is a reserved system label; linker will resolve it
      to the default exception handler.
    * `R0` is a reserved read-only register that holds 0. This variation passes all ergs to the callee.
"""
],
summary = r"""
Reserves a portion of the currently available ergs for a new function instance
and calls the code inside the current contract space.""",
semantic = r"""
Reminder: the *callee* is the function that we call; the *caller* is the
currently executing function where a call takes place. In other words, the
caller calls the callee.

1. Read the value of `abi_reg` and decode the following structure from [%NearCallABI] from it.
   The `ergs_passed` field indicates the amount of ergs we intend to pass, but
   the actual amount of ergs passed gets decided at runtime (see step 2).

   ```
   Record params := { ergs_passed: u32; }.
   ```

   The actual amount of passed ergs is determined by [%split_ergs_callee_caller]
   based on:

   - The ergs allocated for the caller frame.
   - The value of `ergs_passed`.

2. Decrease the number of ergs in the caller frame.
3. Set up the new frame:
   - new PC is assigned the instruction\'s `callee_address` argument.
   - new exception handler is assigned the instruction's `handler_address` argument.
   - new SP is copied from the old frame as is.
   - the allocated ergs are determined by [%split_ergs_caller_callee] in (2).
4. Clear flags.
""",

usage = r"""
- Set `ergs_passed=0` to pass all available ergs to callee.
- If the first argument is omitted, all available ergs will be passed to callee.

  Explanation: if the first argument is omitted, the assembler implicitly puts
  `r0` in its place. The reserved register `r0` always holds zero, therefore
  `ergs_passed` will be decoded into zero as well.

- No particular calling convention is enforced for near calls, so it can be decided by compiler.

- Can be used for internal system code, like bootloader. For example, wrap a
  pair of AA call + fee payment in any order in such `near_call`, and then
  rollback the entire frame atomically.
""",
similar=f"See {FARCALLS}. They are used to call code in other contracts.",
affectedState = r"""
- Execution stack: a new frame is pushed on top of the execution stack, and the caller frame is changed.
  + Caller frame:
    * Ergs are split between caller and callee frames. See [%split_ergs_callee_caller].
  + New (callee) frame:
    * PC is set to `callee_address`
    * SP is copied to the new frame as is.
    * ergs are set to the actual amount passed. See [%split_ergs_callee_caller].
    * exception handler
- Flags are always cleared."""
))
}}}

Function for [%split_ergs_caller_callee] evaluates as follows:

   - if `ergs_passed` = 0, pass all available ergs to the callee and set
     the `caller_ergs` to zero. Upon the callee's normal return, its unspent
     ergs are returned back to the caller.

   - otherwise, if `caller_ergs` $\geq$ `ergs_passed`, pass exactly
     `ergs_passed`. The `caller_ergs` is set to the unspent amount
     `ergs_passed - caller_ergs`.

   - otherwise, if the call is not affordable (`ergs_passed` $\gt$
     `caller_ergs`), pass all available ergs to the callee.

   Function [%split_ergs_callee_caller] returns a pair of erg values, where:

   - the first component is the amount of ergs actually passed to the callee;
   - the second component is the amount of ergs left to the caller.
   *)

  Definition split_ergs_callee_caller (ergs_passed caller_ergs:ergs) : ergs * ergs :=
    if ergs_passed == zero32 then (caller_ergs, zero32) else
      match caller_ergs - ergs_passed with
      | (false, remaining) => (ergs_passed, remaining)
      | (true, remaining) => (caller_ergs, zero32)
      end.


  Inductive step_nearcall: @instruction bound -> smallstep :=
  | step_NearCall_pass_some_ergs:
    forall (expt_handler call_addr: code_address)
      (passed_ergs callee_ergs caller_ergs: ergs)
      (new_caller:callstack) (new_frame:callstack_common) __flags (cs:callstack) high224 regs ctx pages gs,

      (callee_ergs, caller_ergs) = split_ergs_callee_caller passed_ergs (ergs_remaining cs) ->

      new_caller = ergs_set caller_ergs cs ->
      new_frame = mk_cf expt_handler (sp_get cs) call_addr callee_ergs (gs_revertable gs) ->

      step_nearcall
        (OpNearCall (Some (IntValue (high224, mk_params passed_ergs))) call_addr expt_handler)
        {|
          gs_transient := {|
                           gs_flags        := __flags;
                           gs_callstack    := cs;
                           gs_regs         := regs;
                           gs_context_u128 := ctx;
                           gs_pages        := pages;
                           gs_status       := NoPanic;
                         |};
          gs_global       := gs;
        |}
        {|
          gs_transient := {|
                           gs_flags        := flags_clear;
                           gs_callstack    := InternalCall new_frame new_caller;
                           gs_regs         := regs;
                           gs_context_u128 := ctx;
                           gs_pages        := pages;
                           gs_status       := NoPanic;
                         |};
          gs_global       := gs;
        |}.

End NearCallDefinition.
