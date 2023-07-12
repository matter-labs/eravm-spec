Require Common Memory GPR.

Import Common Memory GPR.

Section Addressing.
  (** # Addressing modes

Instruction formats are described by [%instruction].

**Operands** are entities operated upon by instructions. They serve as sources of data, or as destinations for the results of the instruction execution.

**Addressing mode** refers to the way in which an instruction specifies the location of data that needs to be accessed or operated upon.
This document describes the types of operands; each type corresponds to one or multiple possible addressing modes for an operand. See [%InstructionArguments].

Abstract EraVM supports 8 addressing modes.
Some of them only support reading (indicated by "in"), or writing (indicated by "out").


1. Register (in/out).
2. Imm (in)
3. Code page, relative to GPR (in)
4. Const page, relative to GPR (in)
5. Stack page, relative to GPR (in/out)
6. Stack page, relative to GPR and SP (in/out)
7. Stack page, relative to GPR and SP, with decreasing SP (in)
8. Stack page, relative to GPR and SP, with increasing SP (out)

Note that the current implementation encodes some of these modes in the same way
e.g. mode 7 and mode 8 only differ by *in* or *out* position.

Predicate [%resolve] formalizes resolving operands to immediate values, registers
and memory locations.

[%MemoryOps] formalizes reading and writing to locations.

## Register addressing

Register addressing takes value from one of General Purpose Registers (GPR).
   *)

  Inductive reg_io : Set := Reg (reg:reg_name).

  (** See [%global_state], [%gs_regs].

## Immediate 16-bit value *)

  Inductive imm_in : Set := Imm (imm: u16).

  (** Only for input operands. See [%imm_in], [%in_regimm].

## Address on a code page, relative to a GPR *)

  Inductive code_in : Set := CodeAddr (reg:reg_name) (imm:code_address).

  (** Resolved to $\mathit{(reg + imm)}$.

Code and const pages may coincide in the implementation.

## Address on a const page, relative to a GPR *)
  Inductive const_in: Set := ConstAddr (reg:reg_name) (imm:code_address).

  (** Resolved to $\mathit{(reg + imm)}$. Code and const pages may coincide.

## Address on a stack page, relative to a GPR

 Resolved to $\mathit{(reg + imm)}$.

   *)
  Inductive stack_io : Set :=
  | Absolute (reg:reg_name) (imm: stack_address)

  (** ## Address on a stack page, relative to SP and GPR.

 Resolved to $\mathit{(SP - reg + imm)}$.

 Unlike [%RelSpPop], the direction of offset does not change depending on read/write.
   *)
  | RelSP    (reg:reg_name) (offset: stack_address)
  .

  (** ## Stack page, relative to GPR and SP, with decreasing SP (in)

Resolved to $\mathit{(SP - (reg + imm))}$.

Additionally, after the resolution, SP is modified: SP -= (reg + imm).

If used in [%OpNoOp], the value of SP is modified even if there was no actual
read performed. See [%OpNoOp].

   *)

  Inductive stack_in_only : Set :=
  | RelSpPop (reg:reg_name) (delta: stack_address)
  .

  (** ## Stack page, relative to GPR and SP, with increasing SP (out).

Resolved to $\mathit{(SP + (reg + imm))}$.

Additionally, after the resolution, SP is modified: SP += (reg + imm).

If used in [%OpNoOp], the value of SP is modified even if there was no actual
read performed. See [%OpNoOp].
   *)
  Inductive stack_out_only : Set :=
  | RelSpPush (reg:reg_name) (delta: stack_address)
  .

  Section InstructionArguments.
    (** # Operands

In this section we describe operand types of [%instruction].
There is an hierarchy of these types, ordered by inclusion (see [%Coercions]).
For example, the first argument of [%OpAdd] can use any addressing mode, and its
second argument can only use [%reg] address mode.
Both arguments should accept GPR as a source.
     *)

    Inductive stack_in : Set :=
    | StackInOnly (arg: stack_in_only)
    | StackInAny (arg: stack_io)
    .

    Inductive stack_out: Set :=
    | StackOutOnly (arg: stack_out_only)
    | StackOutAny (arg: stack_io)
    .

    Inductive stack_any : Set :=
    | StackAnyIO (arg: stack_io)
    | StackAnyIn (arg: stack_in_only)
    | StackAnyOut (arg: stack_out_only)
    .

    (* begin details : Utility conversions, click to unfold *)
    Definition stack_in_to_any (s:stack_in) : stack_any :=
      match s with
      | StackInOnly arg => StackAnyIn arg
      | StackInAny arg => StackAnyIO arg
      end.

    Definition stack_out_to_any (s:stack_out) : stack_any :=
      match s with
      | StackOutOnly arg => StackAnyOut arg
      | StackOutAny arg => StackAnyIO arg
      end.
    (* end details *)



    (** This argument type allows for all addressing modes. *)
    Inductive any : Set :=
    | AnyReg  : reg_io   -> any
    | AnyImm  : imm_in   -> any
    | AnyStack: stack_any-> any
    | AnyCode : code_in  -> any
    | AnyConst: const_in -> any
    .

    (** We denote input arguments as $\mathit{in_1}$, $\mathit{in_2}$, and output arguments as $\mathit{out_1}$, $\mathit{out_2}$.

Many instructions have 2 input arguments and 1 output argument.

## *In* arguments

Usually, $\mathit{in_1}$ supports any types of arguments, except for [%RelSpPush].

     *)
    Inductive in_any : Set :=
    | InReg  : reg_io   -> in_any
    | InImm  : imm_in   -> in_any
    | InStack: stack_in -> in_any
    | InCode : code_in  -> in_any
    | InConst: const_in -> in_any
    .

    (* begin details: Inclusion function *)
    Definition in_any_incl (ia: in_any) : any :=
      match ia with
      | InReg x => AnyReg x
      | InImm x => AnyImm x
      | InStack x => AnyStack (stack_in_to_any x)
      | InCode x => AnyCode x
      | InConst x => AnyConst x
      end.

    (* end details *)


    (** Usually, $\mathit{in_2}$ supports only arguments in GPRs. *)
    Definition in_reg : Set := reg_io.

    (** In exotic cases, an input argument may either be a register, or an immediate
value, but not anything else. Currently, only UMA instructions requires such an input
argument; see [%OpHeapRead], [%OpHeapWrite], and similar. *)

    Inductive in_regimm : Set :=
    | RegImmR : reg_io -> in_regimm
    | RegImmI : imm_in -> in_regimm
    .

    (* begin details : Inclusion function *)
    Definition in_regimm_incl (ri: in_regimm) : in_any :=
      match ri with
      | RegImmR r => InReg r
      | RegImmI i => InImm i
      end.
    (* end details *)

    (** ## *Out* arguments

- Output arguments can not be immediate values.
- A single immediate value is not sufficient to identify a memory cell, because we have multiple pages (see [%page]).
- Out arguments can not be code or const addresses either, because [%code_page] and [%const_page] are not writable.
- Usually, the $\mathit{out_1}$ argument can be of any type (except for immediate value).
     *)
    Inductive out_any : Set :=
    | OutReg  : reg_io    -> out_any
    | OutStack: stack_out -> out_any
    .

    (* begin details : Inclusion function *)
    Definition out_any_incl (ia: out_any) : any :=
      match ia with
      | OutReg x => AnyReg x
      | OutStack x => AnyStack (stack_out_to_any x)
      end.
    (* end details *)

    Definition out_reg : Set := reg_io.
  End InstructionArguments.

End Addressing.
(** Therefore, we do not define [%out_regimm], because it is impossible to write
in immediate values. *)

Module Coercions.
  Coercion in_any_incl: in_any >-> any.
  Coercion out_any_incl : out_any >-> any.

  Coercion Imm :  u16 >-> imm_in.
  Coercion InReg :  reg_io >-> in_any.
  Coercion InImm :  imm_in >-> in_any.
  Coercion InStack: stack_in >-> in_any.
  Coercion InCode:  code_in >-> in_any.
  Coercion InConst:  const_in >-> in_any.
  Coercion StackInOnly: stack_in_only >-> stack_in.
  Coercion stack_in_to_any: stack_in >-> stack_any.
  Coercion OutReg : reg_io >-> out_any.
  Coercion OutStack: stack_out >-> out_any.
  Coercion AnyStack: stack_any >-> any.
  Coercion StackOutOnly: stack_out_only >-> stack_out.
  Coercion in_regimm_incl: in_regimm >-> in_any.
  Coercion StackInAny : stack_io >-> stack_in.
End Coercions.
