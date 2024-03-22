(* GENERATED FILE, DO NOT EDIT MANUALLY. *)
From RecordUpdate Require Import RecordSet.
Require isa.Modifiers isa.Assembly Predication.
Import Types Modifiers Predication.

Inductive src_mode :=
| SrcReg
| SrcSpRelativePop
| SrcSpRelative
| SrcStackAbsolute
| SrcImm
| SrcCodeAddr
.

Inductive src_special_mode := | SrcSpecialReg | SrcSpecialImm.

Inductive dst_mode :=
| DstReg
| DstSpRelativePush
| DstSpRelative
| DstStackAbsolute
.
Inductive mod_context: Set := 
  | This
  | Caller
  | CodeAddress
  | Meta
  | ErgsLeft
  | Sp
  | GetContextU128
  | SetContextU128
  | PubdataSpent
  | IncrementTx

.
Inductive mach_opcode : Type := 
| OpLoadPtr  (inc: bool)
| OpJump  (src0_mode: src_mode)
| OpMimicCall  (is_shard: bool) (is_static: bool)
| OpVMMeta 
| OpDiv  (src0_mode: src_mode) (dst0_mode: dst_mode) (swap: mod_swap) (set_flags: mod_set_flags)
| OpSLoad 
| OpAnd  (src0_mode: src_mode) (dst0_mode: dst_mode) (set_flags: mod_set_flags)
| OpContractThis 
| OpInvalid 
| OpSub  (src0_mode: src_mode) (dst0_mode: dst_mode) (swap: mod_swap) (set_flags: mod_set_flags)
| OpNoOp  (src0_mode: src_mode) (dst0_mode: dst_mode)
| OpIncrementTxNumber 
| OpRol  (src0_mode: src_mode) (dst0_mode: dst_mode) (swap: mod_swap) (set_flags: mod_set_flags)
| OpMul  (src0_mode: src_mode) (dst0_mode: dst_mode) (set_flags: mod_set_flags)
| OpSetContextReg 
| OpDelegateCall  (is_shard: bool) (is_static: bool)
| OpRet  (to_label: bool)
| OpEvent  (is_first: bool)
| OpPrecompileCall 
| OpStoreHeap  (src0_mode: src_special_mode) (inc: bool)
| OpShr  (src0_mode: src_mode) (dst0_mode: dst_mode) (swap: mod_swap) (set_flags: mod_set_flags)
| OpPanic  (to_label: bool)
| OpContractCodeAddress 
| OpSStore 
| OpPtrSub  (src0_mode: src_mode) (dst0_mode: dst_mode) (swap: mod_swap)
| OpToL1Message  (is_first: bool)
| OpAuxMutating 
| OpPtrAdd  (src0_mode: src_mode) (dst0_mode: dst_mode) (swap: mod_swap)
| OpNearCall 
| OpLoadHeap  (src0_mode: src_special_mode) (inc: bool)
| OpStoreAuxHeap  (src0_mode: src_special_mode) (inc: bool)
| OpXor  (src0_mode: src_mode) (dst0_mode: dst_mode) (set_flags: mod_set_flags)
| OpStaticRead  (src0_mode: src_special_mode) (inc: bool)
| OpFarCall  (is_shard: bool) (is_static: bool)
| OpGetCapturedContext 
| OpOr  (src0_mode: src_mode) (dst0_mode: dst_mode) (set_flags: mod_set_flags)
| OpPtrPack  (src0_mode: src_mode) (dst0_mode: dst_mode) (swap: mod_swap)
| OpVMErgsLeft 
| OpVMSp 
| OpLoadAuxHeap  (src0_mode: src_special_mode) (inc: bool)
| OpTransientStore 
| OpDecommit 
| OpPtrShrink  (src0_mode: src_mode) (dst0_mode: dst_mode) (swap: mod_swap)
| OpRevert  (to_label: bool)
| OpStaticWrite  (src0_mode: src_special_mode) (inc: bool)
| OpTransientLoad 
| OpShl  (src0_mode: src_mode) (dst0_mode: dst_mode) (swap: mod_swap) (set_flags: mod_set_flags)
| OpRor  (src0_mode: src_mode) (dst0_mode: dst_mode) (swap: mod_swap) (set_flags: mod_set_flags)
| OpContractCaller 
| OpAdd  (src0_mode: src_mode) (dst0_mode: dst_mode) (set_flags: mod_set_flags)
.


(** The definition [%mach_instruction] showcases the layout of instruction
fields. This layout is applied against the instruction's binary representation.
 *)
Section MachInstructionDefinition.
  Context {reg_type imm_type: Type}.
  Record mach_instruction :=
    mk_ins {
        op_code: mach_opcode;
        op_predicate: predicate;
        op_src0: reg_type;
        op_src1: reg_type;
        op_dst0: reg_type;
        op_dst1: reg_type;
        op_imm0: imm_type;
        op_imm1: imm_type;
      }.
  #[export] Instance etaIns : Settable _ := settable! mk_ins < op_code; op_predicate; op_src0; op_src1; op_dst0; op_dst1; op_imm0; op_imm1>.
End MachInstructionDefinition.
