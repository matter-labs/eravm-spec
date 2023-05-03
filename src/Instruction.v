Require Common Memory.

Import Common Memory.
(** * Instructions *)


Inductive exec_conditions_type :=
| IfAlways | IfGT | IfEQ | IfLT | IfGE | IfLE | IfNotEQ | IfGTOrLT.

Inductive common_mods := ModSwap | ModSetFlags | ModEmpty.

Section Instruction.
(* Variable instruction: Set. *)
(* Variable invalid_ins: instruction. *)

Inductive arg_any :=
| ArgReg (reg:reg_name) : arg_any
| ArgImm (imm:u16) : arg_any
| ArgStackPushPop (r:reg_name) (delta: stack_address): arg_any
| ArgStackOffset (r:reg_name) (offset: stack_address): arg_any
| ArgStackAddr (r:reg_name) (imm: stack_address): arg_any
| ArgCodeAddr (r:reg_name) (imm:code_address): arg_any.

Inductive arg_reg :=
| ArgRegOnly:  reg_name -> arg_reg.

Definition arg_reg_incl ar : arg_any :=
  match ar with
  | ArgRegOnly x => ArgReg x
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
      ins_mods: common_mods ;
      ins_cond: exec_conditions_type;
  }.

End Instruction.

Definition ins_invalid :=
  {|
    ins_spec := OpInvalid;
    ins_mods := ModEmpty;
    ins_cond:= IfAlways
  |}.

Definition code_page := code_page instruction ins_invalid.
(*
FIXME is this possible even?
 ArgRegRelative (r:reg_name) (offset:u16): arg_any (* FIXME not u16 *)
 *)
