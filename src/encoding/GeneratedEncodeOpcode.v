(* GENERATED FILE, DO NOT EDIT MANUALLY. *)
Require isa.Modifiers encoding.EncodingUtils.

Import ZArith.
Import GeneratedMachISA Modifiers encoding.EncodingUtils.

Section OpcodeEncoderDefinition.
Coercion encode_dst_mode : dst_mode >-> Z.
Coercion encode_src_mode : src_mode >-> Z.
Coercion encode_src_special_mode : src_special_mode >-> Z.
Coercion encode_swap: mod_swap >-> Z.
Coercion encode_set_flags : mod_set_flags >-> Z.
Coercion Z.b2z: bool >-> Z.

Definition encode_opcode (op:mach_opcode) : Z := 
   match op with 
| OpInvalid => 0
| OpNoOp src dst => 1 + 4 * src + 1 * dst
| OpAdd src dst set_flags => 25 + 8 * src + 2 * dst + set_flags
| OpSub src dst swap set_flags => 73 + 16 * src + 4 * dst + 2 * set_flags + swap
| OpMul src dst set_flags => 169 + 8 * src + 2 * dst + set_flags
| OpDiv src dst swap set_flags => 217 + 16 * src + 4 * dst + 2 * set_flags + swap
| OpJump src => 313 + 1 * src
| OpXor src dst set_flags => 319 + 8 * src + 2 * dst + set_flags
| OpAnd src dst set_flags => 367 + 8 * src + 2 * dst + set_flags
| OpOr src dst set_flags => 415 + 8 * src + 2 * dst + set_flags
| OpShl src dst swap set_flags => 463 + 16 * src + 4 * dst + 2 * set_flags + swap
| OpShr src dst swap set_flags => 559 + 16 * src + 4 * dst + 2 * set_flags + swap
| OpRol src dst swap set_flags => 655 + 16 * src + 4 * dst + 2 * set_flags + swap
| OpRor src dst swap set_flags => 751 + 16 * src + 4 * dst + 2 * set_flags + swap
| OpPtrAdd src dst swap => 847 + 8 * src + 2 * dst + swap
| OpPtrSub src dst swap => 895 + 8 * src + 2 * dst + swap
| OpPtrPack src dst swap => 943 + 8 * src + 2 * dst + swap
| OpPtrShrink src dst swap => 991 + 8 * src + 2 * dst + swap
| OpCall => 1039
| OpContextThis => 1040
| OpContextCaller => 1041
| OpContextCodeAddress => 1042
| OpContextMeta => 1043
| OpContextErgsLeft => 1044
| OpContextSp => 1045
| OpContextGetContextU128 => 1046
| OpContextSetContextU128 => 1047
| OpContextSetErgsPerPubdataByte => 1048
| OpContextIncrementTxNumber => 1049
| OpSload => 1050
| OpSstore => 1051
| OpLogToL1 is_first => 1052 + is_first
| OpLogEvent is_first => 1054 + is_first
| OpLogPrecompile => 1056
| OpFarcall is_shard is_static => 1057 + 2 * is_static + is_shard
| OpDelegate is_shard is_static => 1061 + 2 * is_static + is_shard
| OpMimic is_shard is_static => 1065 + 2 * is_static + is_shard
| OpRet to_label => 1069 + to_label
| OpRevert to_label => 1071 + to_label
| OpPanic to_label => 1073 + to_label
| OpLoadHeap src inc => 1075 + 10 * src + inc
| OpStoreHeap src inc => 1077 + 10 * src + inc
| OpLoadAuxHeap src inc => 1079 + 10 * src + inc
| OpStoreAuxHeap src inc => 1081 + 10 * src + inc
| OpLoadPtr inc => 1083 + inc
  end
.

End OpcodeEncoderDefinition.
