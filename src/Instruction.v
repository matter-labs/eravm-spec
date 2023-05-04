Require Common Memory.

Import Common Memory.

(** In this file we describe:

- how to construct a valid instruction e.g. what are the valid operand types;
- the relationships between instructions and other concepts of zkEVM

TODO The exact binary encoding of instructions is different from the following description and will be explored in a different section.
 *)

(** * Structure of instructions *)

(** ** Inner structure *)

(** This section presents a high-level description of how to construct a valid instruction.

§1. Instructions have a part common to all instructions, and an instruction-specific part.

§1.1. The common part consists of:
- Opcode: encodes instruction type. See [opcode_specific].
- Common modifiers: alters the meaning of instruction. See [common_mod], [ins_mods].

    - `swap`: if an instruction has two input operands, this modifier swaps
      them. For example, if `sub in1, in2, out1` computes `in1`-`in2`, `sub`
      with `swap` modifier computes `in2` - `in1`. This is useful because `in1`
      has richer address modes: it can be e.g. fetched from stack, whereas `in2`
      can only be fetched from a register.
    - `set_flags`: after its operation, instruction clears the flags that it has not set.
      For example, the instruction `binop` sets the flag EQ if the result is
      equal to zero. When `set_flags` is applied, `binop` additionally clears
      all other flags after that.
 *)

Record common_mod : Set := mk_cmod {
                               cm_swap: bool;
                               cm_set_flags: bool
                             }.
(** - Condition of execution: instruction is executed only if the currently set
flags are compatible with the condition. Each instruction has a condition
encoded inside it. See [ins_mods], [global_state], [gs_flags]. *)

Inductive exec_conditions_type :=
| IfAlways | IfGT | IfEQ | IfLT | IfGE | IfLE | IfNotEQ | IfGTOrLT.

(** This common part is described by [instruction].

§1.2. Additionally, depending on [opcode_specific], an instruction may have:

- Exclusive modifiers: alter the meaning of instruction, e.g. [binop_mod].
- Operands: up to two input operands `in1` and `in2`, and up to two output operands `out1` and `out2`. Their allowed formats are systematized in the section Addressing Modes.

 *)


(* Create a namespace for argument format description. *)
Module Arg.

  (** ** Addressing modes *)

  (** §1. There are 7 main types of instruction arguments, differentiated by the way they are addressed. See [any].

§1.1. Register, taking a value from one of GPR. See [global_state], [gs_regs].
   *)

  Inductive reg : Set := Reg (reg:reg_name).

  (** §1.2. Immediate 16-bit value. *)
  Inductive imm : Set := Imm (imm: u16).

  (** §1.3. Address on a code page, relative to a GPR. Resolved to (reg + imm). Code and const pages may coincide. *)
  Inductive code : Set := CodeAddr (reg:reg_name) (imm:code_address).

  (** §1.4. Address on a const page, relative to a GPR. Resolved to (reg + imm). Code and const pages may coincide. *)
  Inductive const: Set := ConstAddr (reg:reg_name) (imm:code_address).

  (**
§1.5. Address on a stack page, relative to a GPR. Resolved to (reg + imm).

§1.6. Address on a stack page, relative to SP and GPR. Resolved to (SP - reg + imm).

   *)
  Inductive stack : Set :=
  | Absolute (reg:reg_name) (imm: stack_address): stack
  | RelativeSP (reg:reg_name) (offset: stack_address): stack
  | RelativeSPWithPushPop (reg:reg_name) (delta: stack_address): stack
  (**
§1.7. An effectful operand with implicit SP modification.

§1.7.1. As in the previous case, it is an address on a stack page, relative to SP and GPR; the direction of the offset depends on the operation:

§1.7.1.1 For input operand (reading), it is resolved to (SP - (reg + imm)).

§1.7.1.1.1 Additionally, after the resolution, SP is modified: SP -= (reg + imm).

§1.7.1.2. For output operand (writing), it is resolved to (SP + (reg + imm)).

§1.7.1.2.1 Additionally, after the resolution, SP is modified: SP += (reg + imm).

§1.7.2. If both `in1` and `out1` are using this addressing mode, then both effects are applied in order: first, the `in` effect, then the `out` effect. See an example in [OpNoOp].


§1.7.3. If the instruction uses SP value somehow, then it will see the value AFTER the effects produced by resolution of `in1` and/or `out1`.

§1.7.4. If used in [OpNoOp], the value of SP is modified even if there was no actual read performed. See [OpNoOp].
   *)

  .


  (** All these types are collected in the following definition. *)
  Inductive any : Set :=
  | ArgReg  : reg   -> any
  | ArgImm  : imm   -> any
  | ArgStack: stack -> any
  | ArgCode : code  -> any
  | ArgConst: const -> any
  .

  (**

Consult [opcode_specific] to see a precise instruction format and its allowed arguments.

§2. We denote input arguments as `in1`, `in2`, and output arguments as `out1`, `out2`.

§2.1 Most instructions have 1 or 2 input arguments and 1 or 2 output arguments.

§2.2. Usually `in1` supports any types of arguments.
   *)
  Inductive in_any : Set :=
  | InReg  : reg   -> in_any
  | InImm  : imm   -> in_any
  | InStack: stack -> in_any
  | InCode : code  -> in_any
  | InConst: const -> in_any
  .

  (* An inclusion into [any] type. *)
  Definition in_any_incl (ia: in_any) : any :=
    match ia with
    | InReg x => ArgReg x
    | InImm x => ArgImm x
    | InStack x => ArgStack x
    | InCode x => ArgCode x
    | InConst x => ArgConst x
    end.

  Inductive regonly : Set :=
  | RegOnly  : reg -> regonly
  .

  (** §2.3. `in2` only supports arguments in registers. *)
  Definition in_reg : Set := regonly.

  Definition in_regonly_incl (ro: regonly) : any :=
    match ro with | RegOnly r => ArgReg r end.

  (** §2.4. In exotic cases, an input argument may either be a register, or an
immediate value, but not anything else. Currently, only `uma` requires such an
input argument. *)
  Inductive regimm : Set :=
  | RegImmR : reg -> regimm
  | RegImmI : imm -> regimm
  .
  Definition in_regimm : Set := regimm.

  Definition in_regimm_incl (ri: regimm) : any :=
    match ri with
    | RegImmR r => ArgReg r
    | RegImmI i => ArgImm i
    end.

  (**
§2.5. "Out" arguments can not be immediate values.

§2.5.1. Also, a single immediate value is not enough to identify a memory cell, because we have multiple pages (see [memory_page].

§2.5.1. "Out" arguments can not be code or const addresses either, because these memory regions are not writable.

§2.6. Usually, the `out1` argument can be of any type (except for immediate value).
   *)
  Inductive out_any : Set :=
  | OutReg  : reg   -> out_any
  | OutStack: stack -> out_any
  .

  Definition out_any_incl (ia: out_any) : any :=
    match ia with
    | OutReg x => ArgReg x
    | OutStack x => ArgStack x
    end.

  Definition out_reg : Set := regonly.
  Definition out_reg_incl (ro: regonly) : any :=
    match ro with | RegOnly r => ArgReg r end.

  (* §2.7. Therefore, we do not define [out_regimm], because out arguments can not be immediate values. *)

End Arg.

(** * Exclusive modifiers *)
Section ModifiersExclusive.
(** This section describes all exclusive modifiers of instructions. *)
Inductive binop_mod: Set :=
| BinOpAnd
| BinOpOr
| BinOpXor.

End ModifiersExclusive.

(** * Instructions *)
Section Def.
  Import Arg.

  (** This section describes the syntax of instructions. The instruction
  semantics is described in a different place; see [step]. *)
  Inductive opcode_specific : Set :=
  (** ** Invalid operation*)
  | OpInvalid

  (** TODO short description. *)
  (** ** NoOp *)
  | OpNoOp: in_any -> in_reg -> out_any -> out_reg -> opcode_specific
  (**

Usage:

- Executed when an actual instruction is skipped. All instructions are predicated on [exec_conditions_type]. If current flags are not compatible with the condition, `noop` is executed instead.
- Adjusting stack pointer. The arguments of [OpNoOp] are ignored but the effects of [RelativeSPWithPushPop] on SP still take place. For example, consider the following instruction:

<<
Check OpNoOp
    (InStack (RelativeSPWithPushPop R1 (u16_of 10%Z)))  (* in1 *)
    (RegOnly (Reg R0))                                  (* in2 *)
    (OutStack (RelativeSPWithPushPop R2 (u16_of 20%Z))) (* out1 *)
    (RegOnly (Reg R0)).                                 (* out2 *)
>>


Here, operands `in1` and `out1` are using [RelativeSPWithPushPop] addressing mode.
Therefore, executing this instruction will modify SP like that: first, [sp -= (r1 + 10)]; then, [sp += (r2 + 20)].

This instruction has operands, but performs no operations with memory or registers, except the

one. Both operands which can be Does not perform anything, but the operands in [Arg.Stack] addressing mode may be used to 
- Adjust
       *)
  (** ** BinOp *)
  | OpBinOp : in_any -> in_reg -> out_any -> binop_mod -> opcode_specific
  (**
   Usage:

- Depending on the exclusive modifier, 
   *)
  (** ** Add *)
  | OpAdd: in_any -> in_reg -> out_any -> opcode_specific
  .
  Record instruction : Set :=
    Ins {
        ins_spec: opcode_specific ;
        ins_mods: common_mod ;
        ins_cond: exec_conditions_type;
      }.


  (** A definition for an invalid instruction. It is a default value on code memory pages. See [code_page]. *)
  Definition ins_invalid : instruction :=
    {|
      ins_spec := OpInvalid;
      ins_mods := mk_cmod false false;
      ins_cond:= IfAlways
    |}.

End Def.

(** A helper definition to specialize a code page with a (just defined) instruction type. *)
Definition code_page : Type := code_page instruction ins_invalid.

(* Inner Operation

§1. The _code execution_ in zkEVM is a process of sequential execution of _instructions_.
§1. The register PC holds the [code_address] of the next instruction to be executed. See [global_state], [gs_regs]

§1.1 The instruction is fetched from a [code_page] using [code_address] of 16 bits.


§1.1 The sequentiality is violated by the following instructions:

- jump
- ret
- near and far calls
- TODO: the list is incomplete.

§1.1.1 Note that when an exception occurs, `ret.panic` is executed instead of a currently selected instruction.
 *)
