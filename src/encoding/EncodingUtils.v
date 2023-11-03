Require Common Predication isa.Modifiers isa.GeneratedMachISA.

Import ZBits ZArith.
Import Common GPR GeneratedMachISA Modifiers Predication.

Section EncodingTools.
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
- immediate [%u16] values (2 x 16 bits, big endian)

The precise format is formalized by [%encode_mach_instruction].

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
  | DstStackAbsolute => 3
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

(** 4. Immediate 16-bit values are encoded as-is.

For example, the instruction `sub r0, r1, r2` will be encoded as
`000000000210004B`, which, in binary form, is:

```
0000000000000000 0010 0001 0000 000 00 00001001011
```

Let's break it down:

```
| 0000000000000000 -> imm1
| 0000000000000000 -> imm0
| 0000 -> Dst1: R0 (4 bits, ignored)
| 0010 -> Dst0: R2 (4 bits)
| 0001 -> Src1: R1 (4 bits)
| 0000 -> Src0: R0 (4 bits)
| 000 -> Predicate: IfAlways (3 bits)
| 00 -> Reserved (2 bits)
|  00001001011 -> Opcode (11 bits)
```


Another example: `sub stack=[r1+15], r2, stack+=[r3+63]` is encoded as:
`003f000f0321007d`, which, in binary form, is:

```
0000 0000 0011 1111 0000 0000 0000 1111 0000 0011 0010 0001 0000 0000 0111 1101
```


Let's break it down:

```
| 0000 0000 0011 1111  -> imm1: 63
| 0000 0000 0000 1111 -> imm0: 15
| 0000 -> dst1: R0 (4 bits, ignored)
| 0011 -> dst0: R3 (4 bits)
| 0010 -> src1: R2 (4 bits)
| 0001 ->  src0: R1 (4 bits)
| 000 -> Predicate: IfAlways (3 bits)
| 00 -> Reserved (2 bits)
| 000 0111 1101 -> Opcode (11 bits)
```

Be careful with the big-endian byte order in multibyte numbers.

*)
End EncodingTools.
