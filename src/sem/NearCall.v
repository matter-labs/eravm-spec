From RecordUpdate Require Import RecordSet.
Require SemanticCommon.

Import Addressing Common Condition ExecutionStack Ergs MemoryOps Memory Instruction State ZMod
  ABI ABI.NearCall Addressing.Coercions SemanticCommon.

(**

## NearCall

### Abstract Syntax

```
| OpNearCall    (in1: in_reg) (dest: imm_in) (handler: imm_in)
```

### Syntax

- `call abi_reg, callee_address, exception_handler` as a fully expanded form.
- `call abi_reg, callee_address`
  + The assembler expands this variation to 
    `call abi_reg, callee_address, DEFAULT_UNWIND_DEST`. Here:
    * `DEFAULT_UNWIND_DEST` is a reserved system label; the linker will resolve it
      to the default exception handler.
- `call callee_address` is a simplified form.
  + Assembler expands this variation  to 
    `call r0, callee_address, DEFAULT_UNWIND_DEST`, where:
    * `DEFAULT_UNWIND_DEST` is a reserved system label; linker will resolve it
      to the default exception handler.
    * `R0` is a reserved read-only register that holds 0. This variation passes all ergs to the callee.

### Summary

Reserves a portion of the currently available ergs for a new function instance
and calls the code inside the current contract space.

### Semantic

Reminder: the *callee* is the function that we call; the *caller* is the
currently executing function where a call takes place. In other words, the
caller calls the callee.

Step-by-step explanation:

1. Read the value of `abi_reg` and decode the following structure [ABI.NearCall.params] from it.
   The `ergs_passed` field indicates the amount of ergs we intend to pass, but
   the actual amount of ergs passed gets decided at runtime (see step 2).

```
Record params := {
   ergs_passed: u32;
}.
```

2. The actual amount of ergs passed is determined by [split_ergs_callee_caller] based on:

   - The current balance of the caller frame.
   - The value of `ergs_passed`.
 *)

Definition split_ergs_callee_caller (ergs_passed balance:ergs) : ergs * ergs :=
  if ergs_passed == zero32 then (balance, zero32) else
    match balance - ergs_passed with
    | (remaining, false) => (ergs_passed, remaining)
    | (remaining, true) => (balance, zero32)
    end.

Section Defs.
  
  (**
Explanation for [split_ergs_caller_callee]:

- if `ergs_passed` = 0, pass all available ergs to the callee and set
  the caller's balance to zero. Upon the callee's normal return, its unspent
  ergs are returned back to the caller.

- otherwise, if `balance` $\geq$ `ergs_passed`, pass exactly
  `ergs_passed`. The caller's balance is set to the unspent amount
  `ergs_passed - balance`.

- otherwise, if the call is not affordable (`ergs_passed` $\gt$
  `balance`), pass all available ergs to the callee.

Function [split_ergs_callee_caller] returns a pair of erg values, where:

- the first component is the amount of ergs actually passed to the callee;
- the second component is the amount of ergs left to the caller.

Note: after a normal return (not `panic`), the remaining ergs are returned to
the caller.

    

3. Decrease the balance of the caller frame.
4. Set up the new frame:
   - new PC is assigned the instruction's `callee_address` argument.
   - new exception handler is assigned the instruction's `handler_address` argument.
   - new SP is copied from the old frame as is.
5. Clear flags.

   *)
  
  Context (regs: regs_state) (pgs: pages) (xstack: execution_stack).

  Let fetch := resolve_fetch_value regs xstack pgs.
  
  Inductive step_nearcall: instruction -> flags_state * execution_stack -> Prop:=
  | step_NearCall_pass_some_ergs:
    forall (abi_params_op:in_reg) (abi_params_value:word)  (expt_handler call_addr: code_address)
      (passed_ergs callee_ergs caller_ergs:ergs)
      (abi_tag: bool)
      (new_caller:callframe) (new_frame:callframe_common),

      fetch abi_params_op (mk_pv abi_tag abi_params_value) ->

      Some passed_ergs = option_map ergs_passed (ABI.(decode) abi_params_value) ->

      (callee_ergs, caller_ergs) = split_ergs_callee_caller passed_ergs (ergs_remaining xstack) ->
      
      new_caller = ergs_set caller_ergs xstack ->
      new_frame = mk_cf expt_handler (sp_get xstack) call_addr callee_ergs ->
      
      step_nearcall (OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler))
        (flags_clear, InternalCall new_frame new_caller).

(**


### Affected parts of VM state

- Execution stack: a new frame is pushed on top of the execution stack, and the caller frame is changed.
  + Caller frame:
    * PC of the caller frame is advanced by one, as in any instruction.
    * Ergs are split between caller and callee frames. See [split_ergs_callee_caller].
  + New (callee) frame:
    * PC is set to `callee_address`
    * SP is copied to the new frame as is.
    * ergs are set to the actual amount passed. See [split_ergs_callee_caller].
    * exception handler
- Flags are always cleared.

### Usage


- Set `ergs_passed=0` to pass all available ergs to callee.
- If the first argument is omitted, all available ergs will be passed to callee.

  Explanation: if the first argument is omitted, the compiler implicitly puts
  `r0` in its place. The reserved register `r0` always holds zero, therefore
  `ergs_passed` will be decoded into zero as well.

- No particular calling convention is enforced for near calls, so it can be decided by compiler.

- Can be used for internal system code, like bootloader. For example, wrap a
  pair of AA call + fee payment in any order in such `near_call`, and then
  rollback the entire frame atomically.

### Similar instructions


- See [OpFarCall], [OpMimicCall], [OpDelegateCall]. They are used to call code of other contracts.
 *)
End Defs.

Inductive step: instruction -> smallstep :=
| step_NearCall:
  forall gs flags pages xstack context_u128 regs (abi_params_op:in_reg) new_flags new_xstack ins,

    step_nearcall regs pages xstack ins (new_flags, new_xstack) ->
    step ins 
         {|
           gs_flags        := flags;
           gs_callstack    := xstack;


           gs_regs         := regs;
           gs_pages        := pages;
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
         {|
           gs_flags        := new_flags;
           gs_callstack    := new_xstack;


           gs_regs         := regs;
           gs_pages        := pages;
           gs_context_u128 := context_u128;
           gs_global       := gs;
         |}
.
