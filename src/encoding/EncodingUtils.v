Require Common Predication isa.Modifiers isa.GeneratedMachISA.

Import ZBits ZArith.
Import Common GPR GeneratedMachISA Modifiers Predication.


Definition encode_predicate (p:predicate) : BITS 3 :=
  # match p with
    | IfAlways => 0
    | IfGT => 1
    | IfLT => 2
    | IfEQ => 3
    | IfGE => 4
    | IfLE => 5
    | IfNotEQ => 6
    | IfGTOrLT => 7
    end
.

Definition encode_src_mode (sm:src_mode) : Z :=
  match sm with
  | SrcReg => 0
  | SrcSpRelativePop => 1
  | SrcSpRelative => 2
  | SrcStackAbsolute => 3
  | SrcImm => 4
  | SrcCodeAddr => 5
  end
.

Definition encode_src_special_mode (sm:src_special_mode) : Z :=
  match sm with
  | SrcSpecialReg => 0
  | SrcSpecialImm => 10
  end
.

Definition encode_dst_mode (sm:dst_mode) : Z :=
  match sm with
  | DstReg => 0
  | DstSpRelativePush => 1
  | DstSpRelative => 2
  | DstSpAbsolute => 3
  end
.
Definition encode_set_flags (m: mod_set_flags) : Z :=
  match m with
  | SetFlags => 1
  | PreserveFlags => 0
  end.
Definition encode_swap(m: mod_swap) : Z :=
  match m with
  | Swap => 1
  | NoSwap =>0
  end
.
Definition unpack {n} (s:option (BITS n)) : BITS n :=
  match s with
  | Some b => b
  | None => # 0
  end
.

Definition encode_reg (name:reg_name) : BITS 4 :=
  # (reg_idx name)
.

Definition encode_reg_opt (name:option reg_name) : BITS 4 :=
  match name with
  | Some name => encode_reg name
  | None => # 0
  end
.
