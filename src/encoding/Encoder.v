From RecordUpdate Require Import RecordSet.
Require
  isa.Modifiers
  isa.GeneratedMachISA
  isa.AssemblyToMach
  encoding.EncodingUtils
  encoding.GeneratedEncodeOpcode.

Import ZArith.
Import Assembly Common GeneratedMachISA GeneratedEncodeOpcode isa.AssemblyToMach Predication EncodingUtils.

Definition encode_mach_instruction (i:mach_instruction) : BITS 64 :=
  match i with
  | mk_ins op_code op_predicate op_src0 op_src1 op_dst0 op_dst1 op_imm0 op_imm1 =>
     let reserved2 := @fromNat 2 0 in
          unpack op_imm1
       ## unpack op_imm0
       ## encode_reg_opt op_dst1
       ## encode_reg_opt op_dst0
       ## encode_reg_opt op_src1
       ## encode_reg_opt op_src0
       ## encode_predicate op_predicate
       ## reserved2
       ## @fromZ 11 (encode_opcode op_code)
  end
.

Definition encode_asm (i:predicated asm_instruction) : option (BITS 64) :=
  option_map encode_mach_instruction (asm_to_mach i)
.
