Require isa.CoreSet.

Import isa.CoreSet Addressing GPR Common.
Section StaticMode.

(** # Static mode

**Static mode** is a mode of execution.

Intuitively, executing code in static mode aims at limiting its effects on the global state, similar to executing pure functions.

If VM is in static mode, attempting to execute instructions affecting global system state results in panic.
Refer to [%forbidden_static] for a full list of instructions forbidden in static mode.

Current mode is determined by the flag [%ecf_is_static] in the [%active_extframe] in [%callstack].

## Entering static mode

To execute the code of a contract in static mode, use one of far call
instructions with a static modifier, for example:

```
OpFarCall (Reg R1) (Reg R2) (Imm zero16) true false
```

The same applies to [%OpMimicCall] and [%OpDelegateCall].

## Exiting static mode

If VM executes a contract $C$ in static mode, the mode will persist until the end of execution of $C$.
If $C$ calls itself or other contracts, these calls will be automatically marked as static, even if the far call instruction was not explicit about it.

There is no other way to exit the static mode.

## Usage

Static mode is unrelated and orthogonal to kernel mode.

Executing a contract $C$ in static mode restricts the changes to the state produced by $C$ or any other code that it might call.


Static calls are guaranteed to preserve the state of storage, will not emit events, or modify the [%gs_context_u128] register.
*)


(** Function [%forbidden_static] returns [%true] if instruction [%ins] is forbidden in static mode. *)
  Context (forbidden := true) (allowed := false) {descr:descr}.
  Definition forbidden_static (ins:@instruction descr) : bool :=
    match ins with
    | OpContextSetContextU128 _
    | OpContextSetErgsPerPubdataByte _
    | OpContextIncrementTxNumber
    | OpSStore _ _
    | OpEvent _ _ _
    | OpToL1Message _ _ _
      => forbidden
    | _ => allowed
    end.

  (** Function [%check_forbidden_static] returns [%false] if:

- an instruction [%ins] is not allowed in static mode, and
- the current mode is static, as indicated by [%static_mode_active].
   *)
  Definition check_forbidden_static
    (ins: instruction)
    (static_mode_active: bool) : bool :=
    if static_mode_active
    then negb (forbidden_static ins)
    else true.

End StaticMode.
