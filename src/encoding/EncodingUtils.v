Require Common Predication isa.Modifiers isa.GeneratedMachISA.

Import ZBits ZArith.
Import Common GPR GeneratedMachISA Modifiers Predication.

(** # Encoding parts of instructions

The encoding of [%asm_instruction] is described in two stages:

1. [%asm_to_mach] describes how fields [%asm_instruction] are mapped to the
   EraVM machine instruction [%mach_instruction]; this describes the instruction
   layout.
2. [%encode_mach_instruction] describes the binary encoding of
   [%mach_instruction].


EraVM instructions [%mach_instruction] are 64 bits wide. Starting from the least significant bit,
they are made of the following parts:

- [%mach_opcode] (11 bits)
- 2 reserved bits
- [%predicate] (3 bits)
- [%reg_name]s (4 x 4 bits)
- immediate [%u16] values (2 x 16 bits)

Their encoding is independent and happens as follows:

1. The [%mach_opcode] packs together the information about
  - the instruction meaning, e.g. is it addition, or call, or something else;
  - its source and destination addressing modes.
    For example, in the encoding of `add r1, r0, r3` the meaning of the register
    [%R1] in the field [%op_src0] is "use the value from register r1 as the first
    operand".
    But in the encoding of `add stack=[r1], r0, r3` the meaning of the register
    [%R1] in the field [%op_src0] is "use the value on the stack page by address R1
    as the first operand".
    This difference is reflected in the [%mach_opcode] field: the addressing modes are encoded by [%encode_src_mode]/[%encode_src_special_mode] (for selected instructions)/[%encode_dst_mode]) and mixed in [%mach_opcode] by [%encode_opcode].

*)
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

(** The definitions [%encode_set_flags] and [%encode_swap] are encoding the
[%mod_set_flags] and [%mod_swap] modifier values as one-bit numbers. *)
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

(** 2. [encode_predicate] maps eight different predicates to their encodings as 3-bit
  binary numbers.
*)
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

(** 3. Registers are encoded by their indices as 4-bit numbers, e.g. register
    [%R3] is encoded as $3 = 0011_2$. The meaning of two source and two
    destination registers depends on the instruction and/or addressing modes. *)
Definition encode_reg (name:reg_name) : BITS 4 :=
  # (reg_idx name)
.

Definition encode_reg_opt (name:option reg_name) : BITS 4 :=
  match name with
  | Some name => encode_reg name
  | None => # 0
  end
.

(** 4. Immediate values are encoded as is. *)
