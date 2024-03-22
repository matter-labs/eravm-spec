Require Addressing Assembly isa.Modifiers CoreSet.
Import Addressing isa.Modifiers CoreSet.

Import Addressing.Coercions.
Section AssemblyToCore.
  (** Syntactically translate [%asm_instruction] to a core [%instruction], preceding execution:

1. apply [%mod_swap] modifier to instructions where applicable;
2. remove the restrictions on operand types e.g. in assembly [%OpAdd] may
   accept the first argument in memory and the second argument only in register,
   but in core set both arguments can be fetched from either memory or registers.
   This simplifies attributing semantic to instructions.
   *)

  Definition to_core (input: Assembly.asm_instruction) : @instruction decoded :=
    match input with
    | Assembly.OpInvalid => OpInvalid
    | Assembly.OpNoOp => OpNoOp
    | Assembly.OpSpAdd in1 (Imm ofs) => @OpSpAdd decoded in1 ofs
    | Assembly.OpSpSub in1 (Imm ofs) => @OpSpSub decoded in1 ofs
    | Assembly.OpJump dest ret_addr => @OpJump decoded dest ret_addr
    | Assembly.OpAnd in1 in2 out1 flags =>
        @OpAnd decoded in1 in2 out1 flags
    | Assembly.OpOr in1 in2 out1 flags =>
        @OpOr decoded in1 in2 out1 flags
    | Assembly.OpXor in1 in2 out1 flags =>
        @OpXor decoded in1 in2 out1 flags
    | Assembly.OpAdd in1 in2 out1 flags =>
        @OpAdd decoded in1 in2 out1 flags
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
    | Assembly.OpMul in1 in2 out1 out2 flags =>
        @OpMul decoded in1 in2 out1 out2 flags
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
    | Assembly.OpStore ptr val mem =>
        @OpStore decoded ptr val mem

    | Assembly.OpNearCall in1 (Imm dest) (Imm handler) => @OpNearCall decoded in1 dest handler
    | Assembly.OpFarCall enc dest (Imm handler) is_static is_shard_provided =>
        @OpFarCall decoded enc dest handler is_static is_shard_provided
    | Assembly.OpMimicCall enc dest (Imm handler) is_static is_shard_provided =>
        @OpMimicCall decoded enc dest handler is_static is_shard_provided
    | Assembly.OpDelegateCall enc dest (Imm handler) is_static is_shard_provided =>
        @OpDelegateCall decoded enc dest handler is_static is_shard_provided
    | Assembly.OpNearRetTo (Imm dest) => OpNearRetTo dest
    | Assembly.OpRet args  => @OpRet decoded  args
    | Assembly.OpNearRevertTo (Imm dest) => @OpNearRevertTo decoded dest
    | Assembly.OpRevert args  => @OpRevert decoded  args
    | Assembly.OpNearPanicTo (Imm label) => @OpNearPanicTo decoded label
    | Assembly.OpPanic  => @OpPanic decoded
    | Assembly.OpLoad ptr res mem  => @OpLoad decoded  ptr res mem
    | Assembly.OpLoadInc ptr res mem inc_ptr => @OpLoadInc decoded  ptr res mem inc_ptr
    | Assembly.OpStoreInc ptr val mem inc_ptr => @OpStoreInc decoded ptr val mem inc_ptr
    | Assembly.OpLoadPointer ptr res  => @OpLoadPointer decoded  ptr res
    | Assembly.OpLoadPointerInc ptr res inc_ptr  => @OpLoadPointerInc decoded  ptr res inc_ptr
    | Assembly.OpContractThis out  => @OpContractThis decoded  out
    | Assembly.OpContractCaller out  => @OpContractCaller decoded  out
    | Assembly.OpContractCodeAddress out  => @OpContractCodeAddress decoded  out
    | Assembly.OpVMMeta out  => @OpVMMeta decoded  out
    | Assembly.OpVMErgsLeft out  => @OpVMErgsLeft decoded  out
    | Assembly.OpVMSP out  => @OpVMSP decoded  out
    | Assembly.OpGetCapturedContext out  => @OpGetCapturedContext decoded  out
    | Assembly.OpSetContextReg in1  => @OpSetContextReg decoded  in1
    | Assembly.OpIncrementTxNumber  => @OpIncrementTxNumber decoded
    | Assembly.OpSLoad in1 out  => @OpSLoad decoded  in1 out
    | Assembly.OpSStore in1 in2 =>
        @OpSStore decoded in1 in2
    | Assembly.OpToL1Message in1 in2 is_first =>
        @OpToL1Message decoded  in1 in2 is_first
    | Assembly.OpEvent in1 in2 is_first =>
        @OpEvent decoded  in1 in2 is_first
    | Assembly.OpPrecompileCall in1 in2 out =>
        @OpPrecompileCall decoded  in1 in2 out
  (* TODO: the following is not implemented yet *)
    | Assembly.OpAuxMutating in1 => @OpAuxMutating decoded in1
    | Assembly.OpTransientStore in1 in2 => @OpTransientStore decoded in1 in2
    | Assembly.OpTransientLoad in1 out1 => @OpTransientLoad decoded in1 out1
    | Assembly.OpDecommit in1 in2 out1 => @OpDecommit decoded in1 in2 out1
    | Assembly.OpStaticWrite in1 in2  => @OpStaticWrite decoded in1 in2
    | Assembly.OpStaticWriteInc in1 in2 out1 => @OpStaticWriteInc decoded in1 in2 out1
    | Assembly.OpStaticRead in1 out1 => @OpStaticRead decoded in1 out1
    | Assembly.OpStaticReadInc in1 out1 out2 => @OpStaticReadInc decoded in1 out1 out2
    end.

End AssemblyToCore.

Module Coercions.
  Coercion to_core: Assembly.asm_instruction >-> CoreSet.instruction.
End Coercions.
