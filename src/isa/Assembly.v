Require Addressing Common Memory Predication isa.Modifiers.

Import Addressing Common Memory Predication Modifiers.


Inductive instruction: Type :=
| OpInvalid
| OpNoOp
| OpSpAdd       (in1: in_reg) (ofs: imm_in)  (* encoded as NoOp with $out_1$ *)
| OpSpSub       (in1: in_reg) (ofs: imm_in) (* encoded as NoOp with $in_1$ *)
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
| OpNearRetTo      (label: code_address)
| OpFarRet         (args: in_reg)

| OpNearRevert
| OpNearRevertTo(label: code_address)
| OpFarRevert   (args: in_reg)
| OpNearPanicTo (label: code_address)
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
| OpSStore         (in1: in_reg) (in2: in_reg)    (swap:mod_swap)
| OpToL1Message    (in1: in_reg) (in2: in_reg)                   (is_first: bool)
| OpEvent          (in1: in_reg) (in2: in_reg)                   (is_first: bool) (swap:mod_swap)
| OpPrecompileCall (in1: in_reg) (in2: in_reg)    (out: out_reg) (swap:mod_swap)
.
