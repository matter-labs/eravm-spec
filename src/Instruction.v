Require Common Memory Ergs.

Import Common Memory Ergs.

(** In this file we describe:

- how to construct a valid instruction e.g. what are the valid operand types;
- the relationships between instructions and other concepts of zkEVM

TODO The exact binary encoding of instructions is different from the following description and will be explored in a different section.
 *)

(** * Structure of instructions *)

(** ** Inner structure *)

(** This section presents a high-level description of how to construct a valid instruction.

§1. Instructions have a part common to all instructions, and an instruction-specific part.

§1.1. The common part [instruction] consists of:
- Opcode: encodes instruction type. See [opcode_specific].
- Common modifiers: alters the meaning of instruction. See [common_mod], [ins_mods].

  1. `swap`: if an instruction has two input operands, this modifier swaps
    them. For example, if `sub in1, in2, out1` computes `in1`-`in2`, `sub` with
    `swap` modifier computes `in2` - `in1`. This is useful because `in1` has
    richer address modes: it can be e.g. fetched from stack, whereas `in2` can
    only be fetched from a register.

  2. `set_flags`: if set, instruction is allowed to change the flags. If
    cleared, the instruction will not touch the flags.

 *)

Inductive mod_swap := Swap | NoSwap.
Inductive mod_set_flags := SetFlags | PreserveFlags.

Record common_mod : Set := mk_cmod {
                               cm_swap: mod_swap;
                               cm_set_flags: mod_set_flags
                             }.
(** - Condition of execution: instruction is executed only if the currently set
flags are compatible with the condition. Each instruction has a condition
encoded inside it. See [flags_activated], [ins_mods], [global_state], [gs_flags]. *)

Inductive cond :=
| IfAlways | IfGT | IfEQ | IfLT | IfGE | IfLE | IfNotEQ | IfGTOrLT.

(** §1.2. Additionally, depending on [opcode_specific], an instruction may have:

- Exclusive modifiers: alter the meaning of instruction, e.g. [binop_mod].
- Operands: up to two input operands `in1` and `in2`, and up to two output operands `out1` and `out2`. Their allowed formats are systematized in the section Addressing Modes.

 *)


(* Create a namespace for argument format description. *)
Module Arg.

  (** ** Addressing modes *)

  (** §1. There are 8 main types of addressing the instruction arguments. Some of them only support reading (indicated by "in"), or writing (indicated by "out").

<<
1. Register (in/out), see §1.1
2. Imm (in), see §1.2
3. Code page, relative to GPR (in), see §1.3
4. Const page, relative to GPR (in), see §1.4
5. Stack page, relative to GPR (in/out), see §1.5
6. Stack page, relative to GPR and SP (in/out), see §1.6
7. Stack page, relative to GPR and SP, with decreasing SP (in), see §1.7
8. Stack page, relative to GPR and SP, with increasing SP (out), see §1.8

Note that other docs may merge the types (7) and (8) into a single addressing mode, but this is rather an implementation detail.

This section details these types.

>>

§1.1. #<b>#Register#</b># addressing takes value from one of General Purpose Registers (GPR).
   *)

  Inductive reg_io : Set := Reg (reg:reg_name).

  (** §1.1.1. See [global_state], [gs_regs]. *)

  (** §1.2. #<b>#Immediate 16-bit #</b># value. *)

  Inductive imm_in : Set := Imm (imm: u16).
  (**
§1.2.1. Only for input operands.

§1.2.2. See [imm_in], [in_regimm].
   *)

  (** §1.3. #<b>#Address on a code page, relative to a GPR.#</b># *)

  Inductive code_in : Set := CodeAddr (reg:reg_name) (imm:code_address).

  (** §1.3.1. Resolved to (reg + imm).

§1.3.2. Code and const pages may coincide.

§1.4. #<b>#Address on a const page, relative to a GPR.#</b># *)
  Inductive const_in: Set := ConstAddr (reg:reg_name) (imm:code_address).

  (**
§1.4.1. Resolved to (reg + imm).

§1.4.2. Code and const pages may coincide.


§1.5. #<b># Address on a stack page, relative to a GPR. #</b>#

§1.5.1. Resolved to (reg + imm).

   *)
  Inductive stack_io : Set :=
  | Absolute (reg:reg_name) (imm: stack_address)

  (**
§1.6. #<b>#Address on a stack page, relative to SP and GPR.#</b>#

§1.6.1. Resolved to (SP - reg + imm).

§1.6.2. Unlike [RelSpPop], the direction of offset does not change depending on read/write.

   *)
  | RelSP    (reg:reg_name) (offset: stack_address)
  .

  (**
§1.7. #<b># Stack page, relative to GPR and SP, with decreasing SP (in) #</b>#.

§1.7.1 Resolved to (SP - (reg + imm)).

§1.7.2 Additionally, after the resolution, SP is modified: SP -= (reg + imm).

§1.7.3. If used in [OpNoOp], the value of SP is modified even if there was no actual read performed. See [OpNoOp].

   *)

  Inductive stack_in_only : Set :=
  | RelSpPop (reg:reg_name) (delta: stack_address)
  .

  (**

§1.8. #<b># Stack page, relative to GPR and SP, with increasing SP (out) #</b>#.

§1.8.1. Resolved to (SP + (reg + imm)).

§1.8.2 Additionally, after the resolution, SP is modified: SP += (reg + imm).

§1.8.3. (Analogous to §1.7.1) If used in [OpNoOp], the value of SP is modified even if there was no actual read performed. See [OpNoOp].
   *)
  Inductive stack_out_only : Set :=
  | RelSpPush (reg:reg_name) (delta: stack_address)
  .


  (**

§1.9. If in instruction `in1` is using [RelSpPop] And `out1` is using [RelSpPush], then both
 effects are applied in order:

- first, the `in` effect,
- then, the `out` effect.

§1.9.1 See an example in [OpNoOp].


§1.9.2. If the instruction uses SP value somehow, then it will see the value AFTER the effects produced by resolution of `in1` and/or `out1`.

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

  (** All these addressing types are collected in the following definition. *)
  Inductive any : Set :=
  | AnyReg  : reg_io   -> any
  | AnyImm  : imm_in   -> any
  | AnyStack: stack_any-> any
  | AnyCode : code_in  -> any
  | AnyConst: const_in -> any
  .

  (**


§2. We denote input arguments as `in1`, `in2`, and output arguments as `out1`, `out2`.
Consult [opcode_specific] to see a precise instruction format and its allowed arguments.

§2.1 Most instructions have 1 or 2 input arguments and 1 or 2 output arguments.

§2.2. Usually `in1` supports any types of arguments.
   *)
  Inductive in_any : Set :=
  | InReg  : reg_io   -> in_any
  | InImm  : imm_in   -> in_any
  | InStack: stack_in -> in_any
  | InCode : code_in  -> in_any
  | InConst: const_in -> in_any
  .

  (* begin details: Inclusion function *)
  (* An inclusion into [any] type. *)
  Definition in_any_incl (ia: in_any) : any :=
    match ia with
    | InReg x => AnyReg x
    | InImm x => AnyImm x
    | InStack x => AnyStack (stack_in_to_any x)
    | InCode x => AnyCode x
    | InConst x => AnyConst x
    end.

  (* end details *)

  Inductive regonly : Set :=
  | RegOnly  : reg_io -> regonly
  .

  (* begin details : Inclusion function *)
  Definition in_regonly_incl (ro: regonly) : in_any :=
    match ro with
    | RegOnly x => InReg x
    end.
  (* end details *)

  (** §2.3. `in2` only supports arguments in registers. *)
  Definition in_reg : Set := regonly.


  (** §2.4. In exotic cases, an input argument may either be a register, or an
immediate value, but not anything else. Currently, only `uma` requires such an
input argument. *)
  Inductive in_regimm : Set :=
  | RegImmR : reg_io -> in_regimm
  | RegImmI : imm_in -> in_regimm
  .

  (* begin details : Inclusion function *)
  Definition in_regimm_incl (ri: in_regimm) : any :=
    match ri with
    | RegImmR r => AnyReg r
    | RegImmI i => AnyImm i
    end.
  (* end details *)

  (**
§2.5. "Out" arguments can not be immediate values.

§2.5.1. Also, a single immediate value is not enough to identify a memory cell, because we have multiple pages (see [memory_page]).

§2.5.2. "Out" arguments can not be code or const addresses either, because these memory regions are not writable.

§2.6. Usually, the `out1` argument can be of any type (except for immediate value).
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

  Definition out_reg : Set := regonly.

  (* begin details : Inclusion function *)
  Definition out_regonly_incl (ro: regonly) : any :=
    match ro with | RegOnly r => AnyReg r end.
  (* end details *)
  (** §2.7. Therefore, we do not define [out_regimm], because out arguments can not be immediate values. *)

  Module Coercions.

  Coercion InReg :  reg_io >-> in_any.
  Coercion InImm :  imm_in >-> in_any.
  Coercion InStack: stack_in >-> in_any.
  Coercion InCode:  code_in >-> in_any.
  Coercion InConst:  const_in >-> in_any.
  Coercion StackInOnly: stack_in_only >-> stack_in.
  Coercion stack_in_to_any: stack_in >-> stack_any.
  Coercion in_any_incl: in_any >-> any.
  Coercion in_regonly_incl : regonly >-> in_any.
  Coercion out_any_incl : out_any >-> any.
  Coercion RegOnly: reg_io >-> regonly.
  Coercion OutReg : reg_io >-> out_any.
  Coercion OutStack: stack_out >-> out_any.
  Coercion AnyStack: stack_any >-> any.
  Coercion StackOutOnly: stack_out_only >-> stack_out. 

  End Coercions.
End Arg.

(** * Exclusive modifiers *)
Section ModifiersExclusive.
  Import ZMod.
  (** This section describes all exclusive modifiers of instructions. *)
  Inductive binop_mod: Set := | BinOpAnd | BinOpOr | BinOpXor.

  Definition binop_func {bits} (m:binop_mod) : int_mod bits -> int_mod bits -> int_mod bits :=
    match m with
    | BinOpAnd => bitwise_and bits
    | BinOpOr  => bitwise_or bits
    | BinOpXor => bitwise_xor bits
    end.

  Inductive far_call_mod: Set := | Normal | Mimic | Delegate.

  Record far_call_exception : Set := mk_far_call_exception {
        fce_input_is_not_pointer_when_expected : bool;
        fce_invalid_code_hash_format : bool;
        fce_not_enough_ergs_to_decommit : bool;
        fce_not_enough_ergs_to_grow_memory : bool;
        fce_malformed_abi_quasi_pointer : bool;
        fce_call_in_now_constructed_system_contract : bool;
        fce_note_enough_ergs_for_extra_far_call_costs : bool;
    }.

End ModifiersExclusive.

(** * Instructions *)
Section Def.
  Import Arg.

  (** This section describes the syntax of instructions. The instruction
semantics is described in a different place; see [step]. *)
  Inductive instruction: Set :=
  | OpInvalid
  | OpNoOp
  | OpSPManip     (in1: in_any) (out1: out_any)
  | OpJump        (dest: in_any)
  | OpAnd         (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
  | OpOr          (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
  | OpXor         (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
  | OpAdd         (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
  | OpSub         (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
  | OpNearCall    (in1: in_reg) (dest: imm_in) (handler: imm_in)
  | OpFarCall     (enc: in_reg) (dest: in_reg) (mod: far_call_mod)

                  (* quasi fat pointer + forwarding mode *)
  | OpRet         (args: in_reg) (label: option code_address)
                  (* quasi fat pointer + forwarding mode *)
  | OpRevert      (args: in_reg) (label: option code_address)
  | OpPanic       (label: option code_address)
  .


  (** ** Common definitions *)

  (**
§1. An instruction type, including:
- opcode-specific part;
- common modifiers allowed to any instruction type;
- execution conditions, describing under which conditions (flags) the instruction will be executed.
   *)
  Record instruction_predicated: Set :=
    Ins {
        ins_spec: instruction;
        ins_cond: cond;
      }.

  (**
§2. Invalid instruction. It is a default value on code memory pages.

§2.1. See [code_page]. It is parameterized by an instruction type for convenience of defining it.
   *)
  Definition instruction_invalid : instruction_predicated :=
    {|
      ins_spec := OpInvalid;
      ins_cond:= IfAlways
    |}.

End Def.

(** §2.2. A helper definition to specialize a code page with a (just defined) instruction type. *)
Definition code_page : Type := code_page instruction_predicated instruction_invalid.


(** * Costs *)
Section Costs.
  Import ZMod ZArith.
  Definition base_cost (ins:instruction) :=
    match ins with
    | OpInvalid => INVALID_OPCODE_ERGS
    | OpNoOp | OpSPManip _ _ => RICH_ADDRESSING_OPCODE_ERGS
    | OpJump _ => RICH_ADDRESSING_OPCODE_ERGS
    | OpAnd _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
    | OpOr _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
    | OpXor _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
    | OpAdd _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
    | OpSub _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
    | OpNearCall _ _ _ => fst (AVERAGE_OPCODE_ERGS + CALL_LIKE_ERGS_COST)
    | OpFarCall _ _ _ => ZMod.int_mod_of 32 (
           2 * VM_CYCLE_COST_IN_ERGS.(int_val _)
            + RAM_PERMUTATION_COST_IN_ERGS.(int_val _)
            + STORAGE_READ_IO_PRICE.(int_val _)
            + CALL_LIKE_ERGS_COST.(int_val _)
            + STORAGE_SORTER_COST_IN_ERGS.(int_val _)
            + CODE_DECOMMITMENT_SORTER_COST_IN_ERGS.(int_val _))%Z

    | OpRet _ _ | OpRevert _ _ | OpPanic _ => AVERAGE_OPCODE_ERGS
    end.

End Costs.
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
