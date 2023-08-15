Require Addressing Assembly isa.Modifiers CoreSet.
Import Addressing isa.Modifiers CoreSet.

Import Addressing.Coercions.
Section AssemblyToCore.
  (**

Syntactically translate [%asm_instruction] to a core [%instruction], preceding execution:

1. apply [%mod_swap] modifier to instructions where applicable;
2. remove the restrictions on operand types e.g. in assembly [%OpAdd] may
   accept the first argument in memory and the second argument only in register,
   but in core set both arguments can be fetched from either memory or registers.
   This simplifies attributing semantic to instructions.
   *)
  Context (swap := @apply_swap in_any).

  Definition to_core (input: Assembly.asm_instruction) : @instruction decoded :=
    match input with
    | Assembly.OpInvalid => OpInvalid
    | Assembly.OpNoOp => OpNoOp
    | Assembly.OpSpAdd in1 (Imm ofs) => @OpSpAdd decoded in1 ofs
    | Assembly.OpSpSub in1 (Imm ofs) => @OpSpSub decoded in1 ofs
    | Assembly.OpJump dest => @OpJump decoded dest
    | Assembly.OpAnd in1 in2 out1 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpAnd decoded in1' in2' out1 flags
    | Assembly.OpOr in1 in2 out1 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpOr decoded in1' in2' out1 flags
    | Assembly.OpXor in1 in2 out1 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpXor decoded in1' in2' out1 flags
    | Assembly.OpAdd in1 in2 out1 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpAdd decoded in1' in2' out1 flags
    | Assembly.OpSub in1 in2 out1 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpSub decoded in1' in2' out1 flags
    | Assembly.OpShl in1 in2 out1 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpShl decoded in1' in2' out1 flags
    | Assembly.OpShr in1 in2 out1 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpShr decoded in1' in2' out1 flags
    | Assembly.OpRol in1 in2 out1 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpRol decoded in1' in2' out1 flags
    | Assembly.OpRor in1 in2 out1 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpRor decoded in1' in2' out1 flags
    | Assembly.OpMul in1 in2 out1 out2 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpMul decoded in1' in2' out1 out2 flags
    | Assembly.OpDiv in1 in2 out1 out2 swap flags =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpDiv decoded in1' in2' out1 out2 flags
    | Assembly.OpPtrAdd in1 in2 out swap =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpPtrAdd decoded in1' in2' out
    | Assembly.OpPtrSub in1 in2 out swap =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpPtrSub decoded in1' in2' out
    | Assembly.OpPtrShrink in1 in2 out swap =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpPtrShrink decoded in1' in2' out
    | Assembly.OpPtrPack in1 in2 out swap =>
        let (in1', in2') := apply_swap swap in1 in2 in
        @OpPtrPack decoded in1' in2' out
    | Assembly.OpStore ptr val mem swap =>
        let (ptr', val') := @apply_swap in_any swap ptr val in
        @OpStore decoded ptr' val' mem

    | Assembly.OpNearCall in1 (Imm dest) (Imm handler) => @OpNearCall decoded in1 dest handler
    | Assembly.OpFarCall enc dest (Imm handler) is_static is_shard_provided swap =>
        let (enc', dest') := @apply_swap in_any swap enc dest in
        @OpFarCall decoded enc' dest' handler is_static is_shard_provided
    | Assembly.OpMimicCall enc dest (Imm handler) is_static is_shard_provided swap =>
        let (enc',dest') := @apply_swap in_any swap enc dest in
        @OpMimicCall decoded enc' dest' handler is_static is_shard_provided
    | Assembly.OpDelegateCall enc dest (Imm handler) is_static is_shard_provided swap =>
        let (enc', dest') := @apply_swap in_any swap enc dest in
        @OpDelegateCall decoded enc' dest' handler is_static is_shard_provided
    | Assembly.OpNearRet => OpNearRet
    | Assembly.OpNearRetTo (Imm dest) => OpNearRetTo dest

    | Assembly.OpFarRet args  => @OpFarRet decoded  args
    | Assembly.OpNearRevert  => @OpNearRevert decoded
    | Assembly.OpNearRevertTo (Imm dest) => @OpNearRevertTo decoded dest
    | Assembly.OpFarRevert args  => @OpFarRevert decoded  args
    | Assembly.OpNearPanicTo (Imm label) => @OpNearPanicTo decoded label
    | Assembly.OpPanic  => @OpPanic decoded
    | Assembly.OpLoad ptr res mem  => @OpLoad decoded  ptr res mem
    | Assembly.OpLoadInc ptr res mem inc_ptr => @OpLoadInc decoded  ptr res mem inc_ptr
    | Assembly.OpStoreInc ptr val mem inc_ptr  swap =>
        let (ptr', val') := @apply_swap in_any swap ptr val in
        @OpStoreInc decoded ptr' val' mem inc_ptr
    | Assembly.OpLoadPointer ptr res  => @OpLoadPointer decoded  ptr res
    | Assembly.OpLoadPointerInc ptr res inc_ptr  => @OpLoadPointerInc decoded  ptr res inc_ptr
    | Assembly.OpContextThis out  => @OpContextThis decoded  out
    | Assembly.OpContextCaller out  => @OpContextCaller decoded  out
    | Assembly.OpContextCodeAddress out  => @OpContextCodeAddress decoded  out
    | Assembly.OpContextMeta out  => @OpContextMeta decoded  out
    | Assembly.OpContextErgsLeft out  => @OpContextErgsLeft decoded  out
    | Assembly.OpContextSp out  => @OpContextSp decoded  out
    | Assembly.OpContextGetContextU128 out  => @OpContextGetContextU128 decoded  out
    | Assembly.OpContextSetContextU128 in1  => @OpContextSetContextU128 decoded  in1
    | Assembly.OpContextSetErgsPerPubdataByte in1  => @OpContextSetErgsPerPubdataByte decoded  in1
    | Assembly.OpContextIncrementTxNumber  => @OpContextIncrementTxNumber decoded
    | Assembly.OpSLoad in1 out  => @OpSLoad decoded  in1 out
    | Assembly.OpSStore in1 in2  swap =>
        let (in1', in2') := @apply_swap in_any swap in1 in2 in
        @OpSStore decoded in1' in2'
    | Assembly.OpToL1Message in1 in2 is_first  => @OpToL1Message decoded  in1 in2 is_first
    | Assembly.OpEvent in1 in2 is_first swap =>
        let (in1', in2') := @apply_swap in_any swap in1 in2 in
        @OpEvent decoded  in1' in2' is_first
    | Assembly.OpPrecompileCall in1 in2 out swap  =>
        let (in1', in2') := @apply_swap in_any swap in1 in2 in
        @OpPrecompileCall decoded  in1' in2' out
    end.

End AssemblyToCore.

Module Coercions.
  Coercion to_core: Assembly.asm_instruction >-> CoreSet.instruction.
End Coercions.
