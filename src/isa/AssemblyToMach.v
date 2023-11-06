From RecordUpdate Require Import RecordSet.
Require GeneratedMachISA.
Require Addressing isa.Modifiers isa.Assembly Predication.
Import ssreflect.
Import RecordSetNotations.
Import Assembly Addressing Common GeneratedMachISA Modifiers TransientMemory Pointer Predication.
Import Addressing.Coercions.

(** # Encoding of [%asm_instruction] to the universal instruction layout

In the lowest level, all instructions are encoded to a uniform 64-bit format;
its fields are described by [%mach_instruction].

This file details the encoding of [%asm_instruction] to [%mach_instruction].
 *)
Definition src_mode_of (op:in_any) :=
  match op with
  | InReg x => SrcReg
  | InImm x => SrcImm
  | InStack (StackInOnly (RelSpPop _ _)) => SrcSpRelativePop
  | InStack (StackInAny (Absolute _ _)) => SrcStackAbsolute
  | InStack (StackInAny (RelSP _ _)) => SrcSpRelative
  | InCode x => SrcCodeAddr
  | InConst x => SrcCodeAddr
  end
.
Definition src_special_mode_of (op:in_regimm) :=
  match op with
  | RegImmR x => SrcSpecialReg
  | RegImmI x => SrcSpecialImm
  end
.
Definition dst_mode_of (op:out_any) :=
  match op with
  | OutReg x => DstReg
  | OutStack (StackOutOnly (RelSpPush _ _)) => DstSpRelativePush
  | OutStack (StackOutAny (Absolute _ _)) => DstStackAbsolute
  | OutStack (StackOutAny (RelSP _ _)) => DstSpRelative
  end
.
#[local]
  Coercion src_mode_of:  in_any >-> src_mode.
#[local]
  Coercion src_special_mode_of:  in_regimm >-> src_special_mode.
#[local]
  Coercion dst_mode_of:  out_any >-> dst_mode.

(** The Opcode field includes information such as modifiers and addressing modes. *)
Definition opcode_of (ins: asm_instruction) : mach_opcode :=
  let no_label := false in
  let with_label := true in
  let no_inc := false in
  let inc := true in
  match ins with
  | Assembly.OpInvalid => OpInvalid
  | Assembly.OpNoOp
  | Assembly.OpSpAdd _ _ => OpNoOp SrcReg DstSpRelativePush
  | Assembly.OpSpSub _ _ => OpNoOp SrcSpRelativePop DstReg
  | Assembly.OpJump dest => OpJump dest
  | Assembly.OpAnd src0 _ out sflags => OpAnd src0 out sflags
  | Assembly.OpOr src0 _ out sflags => OpOr src0 out sflags
  | Assembly.OpXor src0 _ out sflags => OpXor src0 out sflags
  | Assembly.OpAdd src0 _ out sflags => OpAdd src0 out sflags
  | Assembly.OpSub src0 src1 dst swap sflags => OpSub src0 dst swap sflags
  | Assembly.OpShl src0 src1 dst swap sflags => OpShl src0 dst swap sflags
  | Assembly.OpShr src0 src1 dst swap sflags => OpShr src0 dst swap sflags
  | Assembly.OpRol src0 src1 dst swap sflags => OpRol src0 dst swap sflags
  | Assembly.OpRor src0 src1 dst swap sflags => OpRor src0 dst swap sflags
  | Assembly.OpMul src0 _ dst0 _ sflags => OpMul src0 dst0 sflags
  | Assembly.OpDiv src0 _ dst0 _ swap sflags => OpDiv src0 dst0 swap sflags
  | Assembly.OpNearCall _ _ _ =>  OpCall
  | Assembly.OpFarCall enc dest handler is_static is_shard_provided => OpFarcall is_static is_shard_provided
  | Assembly.OpMimicCall _ _ _ is_static is_shard_provided => OpMimic is_static is_shard_provided
  | Assembly.OpDelegateCall _ _ _ is_static is_shard_provided => OpDelegate is_static is_shard_provided
  | Assembly.OpNearRet => OpRet no_label
  | Assembly.OpNearRetTo _ => OpRet with_label
  | Assembly.OpFarRet _ => OpRet with_label
  | Assembly.OpNearRevert => OpRevert no_label
  | Assembly.OpNearRevertTo _ => OpRevert with_label
  | Assembly.OpFarRevert _ => OpRevert no_label
  | Assembly.OpNearPanicTo _ => OpPanic with_label
  | Assembly.OpPanic => OpPanic no_label
  | Assembly.OpPtrAdd src0 _ dst0 swap => OpPtrAdd src0 dst0 swap
  | Assembly.OpPtrSub src0 _ dst0 swap => OpPtrSub src0 dst0 swap
  | Assembly.OpPtrShrink src0 _ dst0 swap => OpPtrShrink src0 dst0 swap
  | Assembly.OpPtrPack src0 _ dst0 swap => OpPtrPack src0 dst0 swap
  | Assembly.OpLoad src0 dst0 Heap => OpLoadHeap src0 no_inc
  | Assembly.OpLoad src0 dst0 AuxHeap => OpLoadAuxHeap src0 no_inc
  | Assembly.OpLoadInc src0 dst0 Heap _ => OpLoadHeap src0 inc
  | Assembly.OpLoadInc src0 dst0 AuxHeap _ => OpLoadAuxHeap src0 inc
  | Assembly.OpStore src0 _ Heap => OpStoreHeap src0 no_inc
  | Assembly.OpStore src0 _ AuxHeap => OpStoreAuxHeap src0 no_inc
  | Assembly.OpStoreInc  src0 _ Heap _ => OpStoreHeap src0 inc
  | Assembly.OpStoreInc src0 _ AuxHeap _ => OpStoreAuxHeap src0 inc
  | Assembly.OpLoadPointer _ _ => OpLoadPtr no_inc
  | Assembly.OpLoadPointerInc _ _ _ => OpLoadPtr inc
  | Assembly.OpContextThis _ => OpContextThis
  | Assembly.OpContextCaller _ => OpContextCaller
  | Assembly.OpContextCodeAddress _ => OpContextCodeAddress
  | Assembly.OpContextMeta _ => OpContextMeta
  | Assembly.OpContextErgsLeft _ => OpContextErgsLeft
  | Assembly.OpContextSp _ => OpContextSp
  | Assembly.OpContextGetContextU128 _ => OpContextGetContextU128
  | Assembly.OpContextSetContextU128 _ => OpContextSetContextU128
  | Assembly.OpContextSetErgsPerPubdataByte _ => OpContextSetErgsPerPubdataByte
  | Assembly.OpContextIncrementTxNumber => OpContextIncrementTxNumber
  | Assembly.OpSLoad _ _ => OpSload
  | Assembly.OpSStore _ _ => OpSstore
  | Assembly.OpPrecompileCall _ _ _ => OpLogPrecompile
  | Assembly.OpEvent _ _ is_first => OpLogEvent is_first
  | Assembly.OpToL1Message _ _ is_first => OpLogToL1 is_first
  end.

#[local]
Definition set_src0 (src0: in_any) : mach_instruction -> mach_instruction :=
  fun ins =>
    match src0 with
    | InReg (Reg name) => ins <| op_src0 := Some name |>
    | InImm (Imm val) => ins <| op_imm0 := Some val |>
    | InStack (StackInOnly (RelSpPop reg ofs))
    | InStack (StackInAny (Absolute reg ofs) )
    | InStack (StackInAny (RelSP reg ofs) )
    | InCode (CodeAddr reg ofs)
    | InConst (ConstAddr reg ofs) => ins <| op_src0 := Some reg |> <| op_imm0 := Some ofs|>
    end
.

#[local]
Definition set_src0_special (src0: in_regimm) : mach_instruction -> mach_instruction :=
  fun ins =>
    match src0 with
    | RegImmR (Reg name) => ins <| op_src0 := Some name |>
    | RegImmI (Imm val) => ins <| op_imm0 := Some val |>
    end
.

#[local]
Definition set_dst0 (dst0: out_any) : mach_instruction -> mach_instruction :=
  fun ins =>
    match dst0 with
    | OutReg (Reg name) => ins <| op_dst0 := Some name |>
    | OutStack (StackOutOnly (RelSpPush reg ofs))
    | OutStack (StackOutAny (Absolute reg ofs) )
    | OutStack (StackOutAny (RelSP reg ofs) ) =>
        ins <| op_dst0 := Some reg |> <| op_imm1 := Some ofs|>
    end
.

Section AsmToMachConversion.

  Import ssrfun.

  (** The encoding of [%asm_instruction] to [%mach_instruction] happens in two
  stages:

1. Put the information in the fields of [%mach_instruction] but keep ignored fields uninitialized (equal to [%None]).
2. Flatten [%mach_instruction], erasing difference between meaningful and ignored fields. Fields that were equal to [%None] are assigned default values: zero for immediates, [%R0] for registers.
   *)
  Definition asm_to_mach_opt (ins: predicated asm_instruction) : option (@mach_instruction (option GPR.reg_name) (option u16) ):=
    match ins with
    | Ins ins pred =>
        let mk src0 src1 dst0 dst1 imm0 imm1 := mk_ins (opcode_of ins) pred src0 src1 dst0 dst1 imm0 imm1 in
        let template : mach_instruction := mk None None None None None None  in
        match ins with
        | Assembly.OpInvalid
        | Assembly.OpNoOp
        | Assembly.OpPanic
        | Assembly.OpContextIncrementTxNumber
          => Some template
        | Assembly.OpContextSetContextU128 (Reg src0)
        | Assembly.OpContextSetErgsPerPubdataByte (Reg src0) => Some (template <| op_src0 := Some src0 |> )
        | Assembly.OpSpAdd (Reg reg) (Imm ofs)
        | Assembly.OpSpSub (Reg reg) (Imm ofs) => Some (template <| op_src0 := Some reg |> <| op_imm0 := Some ofs |> )
        | Assembly.OpJump dest => Some (set_src0 dest template)
        | Assembly.OpAdd src0 (Reg src1) dst0 _
        | Assembly.OpOr src0 (Reg src1) dst0 _
        | Assembly.OpXor src0 (Reg src1) dst0 _
        | Assembly.OpAnd src0 (Reg src1) dst0 _
        | Assembly.OpSub src0 (Reg src1) dst0 _ _
        | Assembly.OpShl src0 (Reg src1) dst0 _ _
        | Assembly.OpShr src0 (Reg src1) dst0 _ _
        | Assembly.OpRol src0 (Reg src1) dst0 _ _
        | Assembly.OpRor src0 (Reg src1) dst0 _ _
        | Assembly.OpPtrAdd src0 (Reg src1) dst0 _
        | Assembly.OpPtrSub src0 (Reg src1) dst0 _
        | Assembly.OpPtrShrink src0 (Reg src1) dst0 _
        | Assembly.OpPtrPack src0 (Reg src1) dst0 _
          => Some (set_src0 src0 (set_dst0 dst0 (template <| op_src1 := Some src1 |>)))
        | Assembly.OpMul src0 (Reg src1) dst0 (Reg dst1) _
        | Assembly.OpDiv src0 (Reg src1) dst0 (Reg dst1) _ _
          => Some (set_src0 src0 (set_dst0 dst0 (template <| op_src1 := Some src1 |>
                                                                         <| op_dst1 := Some dst1 |>)))

        | Assembly.OpNearCall (Reg arg) (Imm dest) (Imm handler) =>
            Some ({|
                  op_code := opcode_of ins;
                  op_predicate := pred;
                  op_src0 := Some arg;
                  op_src1 := None;
                  op_dst0 := None;
                  op_dst1 := None;
                  op_imm0 := Some dest;
                  op_imm1 := Some handler;
                |})
        | Assembly.OpNearRet
        | Assembly.OpNearRevert => Some template
        | Assembly.OpNearRetTo (Imm dest)
        | Assembly.OpNearPanicTo (Imm dest)
        | Assembly.OpNearRevertTo (Imm dest) => Some (template <| op_imm0 := Some dest |>)
        | Assembly.OpFarRet (Reg args)
        | Assembly.OpFarRevert (Reg args) => Some (template <| op_src0 := Some args |>)

        | Assembly.OpSStore (Reg src0) (Reg src1)
        | Assembly.OpEvent (Reg src0) (Reg src1) _
        | Assembly.OpToL1Message (Reg src0) (Reg src1) _  =>
            Some (template <| op_src0 := Some src0 |> <| op_src1 := Some src1 |>)
        | Assembly.OpSLoad (Reg src0) (Reg dst0) =>
            Some (template <| op_src0 := Some src0 |> <| op_dst0:= Some dst0|>)

        | Assembly.OpContextThis (Reg dst0)
        | Assembly.OpContextCaller (Reg dst0)
        | Assembly.OpContextCodeAddress (Reg dst0)
        | Assembly.OpContextMeta (Reg dst0)
        | Assembly.OpContextErgsLeft (Reg dst0)
        | Assembly.OpContextSp (Reg dst0)
        | Assembly.OpContextGetContextU128 (Reg dst0) =>
            Some (template <| op_dst0:= Some dst0|>)

        | Assembly.OpPrecompileCall (Reg src0) (Reg src1) (Reg dst0) =>
            Some (template <| op_dst0:= Some dst0|>)

        | Assembly.OpFarCall (Reg params) (Reg dest) (Imm handler) _ _
        | Assembly.OpMimicCall (Reg params) (Reg dest) (Imm handler) _ _
        | Assembly.OpDelegateCall (Reg params) (Reg dest) (Imm handler) _ _ =>
            Some (template
                    <| op_src0 := Some params |>
                                    <| op_src1 := Some dest |>
                                                    <| op_imm0 := Some handler |> )

        | Assembly.OpLoad ptr (Reg res) _
        | Assembly.OpStore ptr (Reg res) _ =>
            Some (set_src0_special ptr (template <| op_dst0 := Some res|> ))
        | Assembly.OpLoadPointer (Reg name) (Reg res) =>
            Some (template <| op_src0 := Some name |> <| op_dst0 := Some res|> )
        | Assembly.OpLoadInc ptr (Reg res) _ (Reg inc_ptr)
        | Assembly.OpStoreInc ptr (Reg res) _ (Reg inc_ptr) =>
            Some (set_src0_special ptr (template <| op_dst0 := Some res|> <| op_dst1 := Some inc_ptr |>))

        | Assembly.OpLoadPointerInc (Reg ptr) (Reg res) (Reg inc_ptr) =>
            Some (template <| op_src0 := Some ptr |> <| op_dst0 := Some res|> <| op_dst1 := Some inc_ptr |>)
        end
    end.

  Definition mach_flatten (i:@mach_instruction (option GPR.reg_name) (option u16)) : @mach_instruction GPR.reg_name u16 :=
    let or_r0 := Option.default GPR.R0 in
    let or_zero := Option.default zero16 in
    match i with
    | mk_ins op_code op_predicate op_src0 op_src1 op_dst0 op_dst1 op_imm0 op_imm1 =>
        mk_ins op_code op_predicate
          (or_r0 op_src0)
          (or_r0 op_src1)
          (or_r0 op_dst0)
          (or_r0 op_dst1)
          (or_zero op_imm0)
          (or_zero op_imm1)
    end.

  Definition asm_to_mach (asm_ins: predicated asm_instruction) : option mach_instruction :=
   option_map mach_flatten (asm_to_mach_opt asm_ins).

End AsmToMachConversion.
