Require Common Memory.

Import Common Memory.

(** * Instructions *)

Inductive exec_conditions_type :=
| IfAlways | IfGT | IfEQ | IfLT | IfGE | IfLE | IfNotEQ | IfGTOrLT.

Record common_mod : Set := mk_cmod {
                               cm_swap: bool;
                               cm_set_flags: bool
                             }.

Module Arg.

  (** ** Addressing modes *)

Inductive reg : Set := Reg (reg:reg_name).
Inductive imm : Set := Imm (imm: u16).

Inductive code : Set := CodeAddr (r:reg_name) (imm:code_address).
Inductive const: Set := ConstAddr (r:reg_name) (imm:code_address).

Inductive stack : Set :=
| RelativeSPWithPushPop (r:reg_name) (delta: stack_address): stack
| RelativeSP (r:reg_name) (offset: stack_address): stack
| Absolute (r:reg_name) (imm: stack_address): stack
.

Inductive any : Set :=
| ArgReg  : reg   -> any
| ArgImm  : imm   -> any
| ArgStack: stack -> any
| ArgCode : code  -> any
| ArgConst: const -> any
.

Inductive in_any : Set :=
| InReg  : reg   -> in_any
| InImm  : imm   -> in_any
| InStack: stack -> in_any
| InCode : code  -> in_any
| InConst: const -> in_any
.

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

Definition in_reg : Set := regonly.

Definition in_regonly_incl (ro: regonly) : any :=
  match ro with | RegOnly r => ArgReg r end.

(** The argument may either be a register, or an immediate value.
Only `uma` requires such an input argument.
 *)
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

(** "Out" operands can not be immediate, it differs them from In operands*)
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

(* out_regimm does not exist. *)

End Arg.

Section Instruction.
Import Arg.

Inductive binop_mod: Set := | BinOpAnd | BinOpOr | BinOpXor.

Inductive opcode_specific : Set :=
| OpInvalid
| OpNoOp: in_any-> in_reg -> out_any -> out_reg -> opcode_specific
| OpBinOp : in_any-> in_reg -> out_any -> binop_mod -> opcode_specific
| OpAdd: in_any-> in_reg -> out_any -> opcode_specific
.
Record instruction : Set :=
Ins { ins_spec: opcode_specific ;
      ins_mods: common_mod ;
      ins_cond: exec_conditions_type;
  }.

End Instruction.

Definition ins_invalid : instruction :=
  {|
    ins_spec := OpInvalid;
    ins_mods := mk_cmod false false;
    ins_cond:= IfAlways
  |}.

Definition code_page : Type := code_page instruction ins_invalid.
