Require isa.CoreSet.

Import CoreSet Memory.

Section KernelMode.
  Import ZArith Arith spec.
  Open Scope Z_scope.
  Open Scope ZMod_scope.

  Context {descr: CoreSet.descr}.
  (** # Kernel Mode

EraVM operates either in **kernel** or in **user mode**. Some instructions (see
[%requires_kernel] are only allowed in kernel mode; executing them in user mode
results in panic.

Current mode is determined by the address of the currently executed contract $C$:

- if $C <$ [%KERNEL_MODE_MAXADDR_LIMIT], EraVM is in kernel mode;
- otherwise, EraVM is in user mode.
   *)
  Definition KERNEL_MODE_MAXADDR_LIMIT : contract_address := fromZ (2^16).

  Definition addr_is_kernel (addr:contract_address) : bool :=
    addr < KERNEL_MODE_MAXADDR_LIMIT.

(** Current contract's address can be obtained from the active external frame in [%callstack].
Topmost external frame (active frame) is obtained through [%active_extframe], it contains the current contract's address in its field [%ecf_this_address].

The list of instructions requiring kernel mode is encoded by the
definition [%requires_kernel]. If [%requires_kernel ins == true], the instruction
[%ins] is only allowed in kernel mode. *)
  Definition requires_kernel (ins: @instruction descr) : bool :=
    match ins with
    | OpMimicCall _ _ _ _ _
    | OpContextSetContextU128 _
    | OpContextSetErgsPerPubdataByte _
    | OpContextIncrementTxNumber
    | OpEvent _ _ _
    | OpToL1Message _ _ _
    | OpPrecompileCall _ _ _
      => true
    | _ => false
    end.

  (** Function [%check_requires_kernel] returns [%false] if:

- an instruction [%ins] requires kernel mode, and
- VM is not in kernel mode, as indicated by [%in_kernel].
   *)
  Definition check_requires_kernel
    (ins: @instruction descr)
    (in_kernel: bool) : bool :=
    (negb in_kernel) || in_kernel.

End KernelMode.
