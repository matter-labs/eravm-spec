Require Common Memory.

Import Common Memory.
(** * Instructions *)

Inductive exec_conditions_type :=
| IfAlways | IfGT | IfEQ | IfLT | IfGE | IfLE | IfNotEQ | IfGTOrLT.

Record common_mod : Set := mk_cmod {
                               cm_swap: bool;
                               cm_set_flags: bool
                             }.

Section Instruction.

Inductive arg_reg : Set :=
  | ArgReg (reg:reg_name).

Inductive arg_imm : Set :=
  | ArgImm (imm: u16).

Inductive arg_reg_imm :=
  | ArgRIReg : arg_reg -> arg_reg_imm
  | ArgRIImm : arg_imm -> arg_reg_imm.

Inductive arg_any :=
| ArgAnyReg : arg_reg -> arg_any
| ArgAnyImm : arg_imm -> arg_any
| ArgAnyStackPushPop (r:reg_name) (delta: stack_address): arg_any
| ArgAnyStackOffset (r:reg_name) (offset: stack_address): arg_any
| ArgAnyStackAddr (r:reg_name) (imm: stack_address): arg_any
| ArgAnyCodeAddr (r:reg_name) (imm:code_address): arg_any.


Definition arg_reg_incl : arg_reg -> arg_any := ArgAnyReg.
Definition arg_ri_incl (ari: arg_reg_imm) : arg_any :=
  match ari with
  | ArgRIReg x => ArgAnyReg x
  | ArgRIImm x => ArgAnyImm x
  end.


Inductive binop_mod: Set := | BinOpAnd | BinOpOr | BinOpXor.
Definition in_any := arg_any.
Definition out_any := arg_any.
Definition in_reg := arg_reg.
Definition out_reg := arg_reg.

Inductive opcode_specific :=
| OpInvalid
| OpNoOp: in_any-> in_reg -> out_any -> out_reg -> opcode_specific
| OpBinOp : in_any-> in_reg -> out_any -> binop_mod -> opcode_specific
| OpAdd: in_any-> in_reg -> out_any -> opcode_specific
.
Record instruction :=
Ins { ins_spec: opcode_specific ;
      ins_mods: common_mod ;
      ins_cond: exec_conditions_type;
  }.

End Instruction.

Definition ins_invalid :=
  {|
    ins_spec := OpInvalid;
    ins_mods := mk_cmod false false;
    ins_cond:= IfAlways
  |}.

Definition code_page := code_page instruction ins_invalid.
