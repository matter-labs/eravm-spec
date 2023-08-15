Require Addressing Common Memory Predication isa.Modifiers.

Import Addressing Common Memory Predication Modifiers.

Section AssemblyInstructionSet.
  (**
# EraVM assembly instruction set

This section describes an instruction set [%asm_instruction] which is a target for
compiler.

The type [%asm_instruction] defines instruction format with the precise types of
their operands, and all their supported modifiers.
This set is a slice in the middle of the abstractions hierarchy:

- The next lower level is machine instructions. The assembly encodes [%asm_instruction]
  to the lower-level machine instructions which are then mapped to their binary encodings.
- The next higher level are **core instructions** described in section
  [CoreInstructionSet]. These instructions have are simplified formats, impose
  less constraints on the operand sources and destinations, and do not support
  the [%mod_swap] modifier.

For all practical purposes, the reader of the specification should start at this
level, unless their interest is in lower-level encoding details.

The function [%base_cost] defines the basic costs of each instruction in **ergs**.
   *)

  Inductive asm_instruction: Type :=
  | OpInvalid
  | OpNoOp
  | OpSpAdd       (in1: in_reg) (ofs: imm_in)  (* encoded as NoOp with $out_1$ in address mode [%Addressing.RelSpPush]*)
  | OpSpSub       (in1: in_reg) (ofs: imm_in)  (* encoded as NoOp with $in_1$ in address mode [%Addressing.RelSpPop] *)
  | OpJump        (dest: in_reg)
  | OpAnd         (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap) (flags:mod_set_flags)
  | OpOr          (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap) (flags:mod_set_flags)
  | OpXor         (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap) (flags:mod_set_flags)
  | OpAdd         (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap) (flags:mod_set_flags)
  | OpSub         (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap) (flags:mod_set_flags)

  | OpShl         (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap)  (flags:mod_set_flags)
  | OpShr         (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap)  (flags:mod_set_flags)
  | OpRol         (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap)  (flags:mod_set_flags)
  | OpRor         (in1: in_any) (in2: in_reg)  (out1: out_any)  (swap:mod_swap)  (flags:mod_set_flags)

  | OpMul         (in1: in_any) (in2: in_reg)  (out1: out_any) (out2: out_reg) (swap:mod_swap) (flags:mod_set_flags)
  | OpDiv         (in1: in_any) (in2: in_reg)  (out1: out_any) (out2: out_reg) (swap:mod_swap) (flags:mod_set_flags)
  | OpNearCall    (in1: in_reg) (dest: imm_in) (handler: imm_in)
  | OpFarCall     (enc: in_reg) (dest: in_reg) (handler: imm_in) (is_static:bool) (is_shard_provided: bool) (swap: mod_swap)
  | OpMimicCall   (enc: in_reg) (dest: in_reg) (handler: imm_in) (is_static:bool) (is_shard_provided: bool) (swap: mod_swap)
  | OpDelegateCall(enc: in_reg) (dest: in_reg) (handler: imm_in) (is_static:bool) (is_shard_provided: bool) (swap: mod_swap)

  | OpNearRet
  | OpNearRetTo   (dest: imm_in)
  | OpFarRet      (args: in_reg)

  | OpNearRevert
  | OpNearRevertTo(dest: imm_in)
  | OpFarRevert   (args: in_reg)
  | OpNearPanicTo (dest: imm_in)
  | OpPanic

  | OpPtrAdd      (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)
  | OpPtrSub      (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)
  | OpPtrShrink   (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)
  | OpPtrPack     (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)


  | OpLoad        (ptr: in_regimm) (res: out_reg) (mem:data_page_type)
  | OpLoadInc     (ptr: in_regimm) (res: out_reg) (mem:data_page_type) (inc_ptr: out_reg)
  | OpStore       (ptr: in_regimm) (val: in_reg)  (mem:data_page_type)                    (swap:mod_swap)
  | OpStoreInc    (ptr: in_regimm) (val: in_reg)  (mem:data_page_type) (inc_ptr: out_reg) (swap: mod_swap)


  | OpLoadPointer     (ptr: in_reg)  (res: out_reg)
  | OpLoadPointerInc  (ptr: in_reg)  (res: out_reg) (inc_ptr: out_reg)


  | OpContextThis                                   (out: out_reg)
  | OpContextCaller                                 (out: out_reg)
  | OpContextCodeAddress                            (out: out_reg)
  | OpContextMeta                                   (out: out_reg)
  | OpContextErgsLeft                               (out: out_reg)
  | OpContextSp                                     (out: out_reg)
  | OpContextGetContextU128                         (out: out_reg)
  | OpContextSetContextU128        (in1: in_reg)
  | OpContextSetErgsPerPubdataByte (in1: in_reg)
  | OpContextIncrementTxNumber


  | OpSLoad          (in1: in_reg)                  (out: out_reg)
  | OpSStore         (in1: in_reg) (in2: in_reg)                   (swap:mod_swap)

  | OpPrecompileCall (in1: in_reg) (in2: in_reg)    (out: out_reg) (swap:mod_swap)

  | OpEvent          (in1: in_reg) (in2: in_reg)                   (is_first: bool) (swap:mod_swap)
  | OpToL1Message    (in1: in_reg) (in2: in_reg)                   (is_first: bool)
  .

End AssemblyInstructionSet.
