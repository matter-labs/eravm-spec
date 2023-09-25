Require Core Addressing CallStack .

Import ssreflect ssrfun ssrbool eqtype ssreflect.tuple.
Import Addressing Core Common ZArith CallStack GPR Memory PrimitiveValue.

Section AddressingUtils.
  Import MemoryBase.
  Open Scope ZMod_scope.
  (** Predicate [%reg_rel] implements the resolution for register-based relative addressing. Its specializations implement relative addressing for:

- the [%code_page]: [%reg_rel_code];
- the [%const_page]: [%reg_rel_const];
- the [%stack_page]: [%reg_rel_const];
   *)

  (* Inductive equal_bits {n m} (x :BITS n) (y: BITS m) (H: n = m) : Prop := *)

  Definition low16 (w: word) : u16 := low 16 w.
  Definition low32 (w: word) : u32 := low 32 w.

  Inductive reg_rel : regs_state -> reg_name -> u16 -> u16 -> Prop :=
  | rca_code_pp: forall regs reg reg_val base ofs
                   abs OF_ignored,
      fetch_gpr regs reg = IntValue reg_val ->
      base = low16 reg_val  ->
      base + ofs = (OF_ignored, abs) ->
      reg_rel regs reg ofs abs.

  Definition reg_rel_code : regs_state -> reg_name -> u16 -> code_address -> Prop
    := reg_rel.
  Definition reg_rel_const : regs_state -> reg_name -> u16 -> const_address -> Prop
    := reg_rel.
  Definition reg_rel_stack : regs_state -> reg_name -> u16 -> stack_address -> Prop
    := reg_rel.

  (** Note: in [%sp_displ], [%delta = reg + imm]. *)
  Definition sp_displ: regs_state -> reg_name -> u16 -> stack_address -> Prop := reg_rel_stack.
End AddressingUtils.

  (** # Address resolution

Instructions have multiple ways of addressing data, i.e. immediate 16-bit
values, GPRs, absolute or relative addresses in stack etc. They are described in
section [%Addressing] by types such as [%in_any], [%out_reg], and so on.

**Location** stands for a source and/or destination for data, addressable by instructions.

**Address resolution** is a matching between instruction operands and locations using the supported address modes.

There are five main locations that instructions can address:

1. Immediate data: the operand is provided directly as an unsigned 16-bit integer value.
2. Register: data can be fetched or stored to general purpose registers [%r1]--[%r15].
3. Stack address: data can be fetched or stored to stack.
4. Code address: instructions can be fetched from a code page.
5. Constant address: data can be fetched from a read-only page holding constant words.

   *)
Inductive loc : Type :=
| LocImm: u16 ->  loc
| LocReg : reg_name ->  loc
| LocStackAddress: stack_address -> loc
| LocCodeAddr: code_address -> loc
| LocConstAddr: const_address ->  loc
.
(** Additionally, data can be fetched and stored to data pages; this process is
more complicated and requires putting in registers specially formed pointers
[%heap_ptr]. *)

Section Resolution.
  Import Addressing.Coercions.

  Open Scope ZMod_scope.

  (** Resolution of [%RelSpPop] and [%RelSpPush] addressing modes modifies the
  stack pointer. This, and possible future effects, is described by
  [%resolve_effect] predicate.
   *)
  Inductive resolve_effect := | NoEffect | NewSP (val: stack_address).

  Record resolve_result :=
    mk_resolved {
        effect: resolve_effect;
        location:> loc;
      }.

  Context {state_checkpoint}
    (callstack := @callstack state_checkpoint)
    (rs:regs_state)
    (cs: callstack)
    (sp:= sp_get cs).

  Reserved Notation "[[ resolved ]]" (at level 9, no associativity).
  Reserved Notation "[[ resolved ; 'SP' <- newsp ]]" (at level 9, no associativity).

  Declare Scope Resolution_scope.
  Open Scope Resolution_scope.


  (** Address resolution is formalized by the predicate [%resolve]. *)
  Inductive resolve : any -> resolve_result -> Prop :=
    (** - Registers and immediate values are resolved to themselves. *)
  | rslv_reg : forall reg,
      resolve (Reg reg) [[ LocReg reg ]]
  | rslv_imm: forall imm,
      resolve  (Imm imm) [[ LocImm imm ]]
(**
- [%Absolute] : Absolute stack addressing with a general purpose register and an immediate
  displacement is resolved to $\mathit{reg}+\mathit{imm}$.
*)
  | rslv_stack_abs: forall regs reg imm abs,
      reg_rel_stack regs reg imm abs ->
      resolve  (Absolute reg imm) [[ LocStackAddress abs ]]
(**
- [%RelSP] : Addressing relative to SP with a general purpose register and an immediate
  displacement is resolved to $\mathit{sp}-(\mathit{reg}+\mathit{imm})$.
*)
  | rslv_stack_rel: forall reg ofs delta_sp sp_rel,
      sp_displ rs reg ofs delta_sp ->

      (false, sp_rel) = sp - delta_sp->
      resolve  (RelSP reg ofs) [[ LocStackAddress sp_rel ]]

(**
- [%RelSpPop] : **Reading** relative to SP with a general purpose register and
  an immediate displacement, **and SP decrement**, is resolved to
  $\mathit{sp}-(\mathit{reg}+\mathit{imm})$; additionally, SP is assigned the
  same value $\mathit{sp}-(\mathit{reg}+\mathit{imm})$. The new SP value will
  then be used for the resolution of other operands.

   In other words, it is equivalent to a sequence of two actions:

   1. SP = SP - (reg + imm)
   2. [SP] -> result

   In other words, it is equivalent to:

   1. pop the stack (reg + imm - 1) times, discard these values
   2. pop value from stack and return it
*)
  | rslv_stack_gpop: forall reg ofs delta_sp new_sp,
      sp_displ rs reg ofs delta_sp ->
      (false, new_sp) = sp - delta_sp->
      resolve  (RelSpPop reg ofs) [[ LocStackAddress new_sp ; SP <- new_sp ]]

(**
- [%RelSpPush] : **Writing** relative to SP with a general purpose register and
  an immediate displacement, **and SP increment**, is resolved to **the current
  value of SP**. Additionally, SP is assigned a new value
  $\mathit{sp}+(\mathit{reg}+\mathit{imm})$. The new SP value will then be used
  for the resolution of other operands.

  In other words, it is equivalent to a sequence of two actions:

  1. [SP] <- input value
  2. SP = SP + (reg + imm)


  In other words, it is equivalent to:

  1. push the input value to the stack
  2. allocate (reg+imm-1) slots in stack
*)
  | rslv_stack_gpush: forall reg ofs delta_sp new_sp,
      sp_displ rs reg ofs delta_sp ->
      (false, new_sp) = sp + delta_sp ->
      resolve  (RelSpPush reg ofs) [[ LocStackAddress sp ; SP <- new_sp ]]

  | rslv_code: forall reg abs_imm addr,
      reg_rel_code rs reg abs_imm addr ->
      resolve  (CodeAddr reg abs_imm) [[ LocCodeAddr addr ]]
  | rslv_const: forall reg abs_imm addr,
      reg_rel_const rs reg abs_imm addr ->
      resolve  (ConstAddr reg abs_imm) [[ LocConstAddr addr ]]
  where
  "[[ resolved ]]" := (mk_resolved NoEffect resolved) : Resolution_scope
  and
  "[[ resolved ; 'SP' <- newsp ]]" := (mk_resolved (NewSP newsp) resolved) : Resolution_scope.

  (** Note: the reason of the asymmetry between [%RelSpPush] and [%RelSpPop] is because they are generalizations of `push` and `pop` operations.

Consider a stack implemented as an array with a pointer. Suppose that, like in EraVM, SP points the the next address after the last value in stack; in other words, the topmost element in the stack is located at $\mathit{sp}-1$. Then `push` and `pop` can be implemented in the following way:

- Push:

  1. [SP] <- new_value
  2. SP = SP + 1

- Pop:

  1. SP = SP - 1
  2. [SP] -> result

This asymmetry naturally generalizes to [%RelSpPush] and [%RelSpPop].


## Using [%RelSpPop] and [%RelSpPush] in one instruction

Suppose an instruction is using both [%RelSpPop] and [%RelSpPush], then both
effects are applied in order:

- First, the "in" effect of [%RelSpPop].
- Then, the "out" effect of [%RelSpPush], where SP is already changed by [%RelSpPop].
- If the instruction accesses SP, both effects will be applied prior to the instruction-specific logic.

See an example in [%sem.ModSP.step].


Predicate [%apply_effects] formalizes the application of address resolution side effects to the state.
In the current state of EraVM, only SP modifications are allowed, therefore the effect is limited to the topmost frame of callstack, which holds the current value of sp in [%cf_sp].
   *)
  Inductive apply_effects : resolve_effect -> callstack -> Prop :=
  | ae_none: forall s,
      apply_effects NoEffect s
  | ae_sp: forall  cs' new_sp,
      sp_map_spec (fun _ => new_sp) cs cs' ->
      apply_effects (NewSP new_sp) cs'.

  Inductive resolve_apply
    : any -> (callstack * loc) -> Prop :=
  | ra_no_effect : forall arg loc,
      resolve arg [[ loc ]] ->
      resolve_apply arg (cs, loc)
  | ra_effect : forall cs' arg loc new_sp,
      resolve arg [[ loc ; SP <- new_sp ]] ->
      sp_map_spec (fun _ => new_sp) cs cs' ->
      resolve_apply arg (cs', loc).

End Resolution.
