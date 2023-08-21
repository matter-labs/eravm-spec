Require Common isa.CoreSet.
Import Common isa.CoreSet.

Section Panics.
  (** # Panic

**Panic** refers to a situation of irrecoverable error.
It can occur for one of the following reasons:

- There are not enough ergs to execute an action.
- Executing an instruction requiring kernel mode in user mode.
- Executing an instruction mutating global state in static mode.
- Violation of one of VM inner invariants.
- Overflow of callstack.
- Attempt to execute an invalid instruction.
-
Providing an integer value (with the tag cleared) instead of a pointer value (with the tag set) to an instruction that expects a tagged fat pointer value, e.g. [%OpPtrAdd].

## Complete list of panic reasons

The type [%reason] describes all situations where EraVM panics.
   *)
  Inductive reason :=
  | NotEnoughErgs
  | NotInKernelMode
  | ForbiddenInStaticMode
  | InvariantViolation
  | CallStackOverflow
  | InvalidInstruction
  | ExpectedPointerInInstruction {descr} (op:@instruction descr)
  | TriggeredExplicitly
  .

  Inductive status :=
  | NoPanic
  | Panic : reason -> status
  .

End Panics.
