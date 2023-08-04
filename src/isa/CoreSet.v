Require Addressing isa.Modifiers Predication.
Import Addressing Modifiers Memory Predication.

Structure descr: Type := {
    src_pv: Type;
    src_fat_ptr: Type;
    src_heap_ptr: Type;
    src_farcall_params: Type;
    src_nearcall_params: Type;
    src_ret_params: Type;
    src_precompile_params: Type;
    dest_pv: Type;
    dest_heap_ptr: Type;
    dest_fat_ptr: Type;
    dest_meta_params: Type;
  }.

Section Functor.

  Context {d: descr}
    (src_pv:= src_pv d)
    (src_fat_ptr:= src_fat_ptr d)
    (src_heap_ptr:= src_heap_ptr d)
    (src_farcall_params:= src_farcall_params d)
    (src_nearcall_params:= src_nearcall_params d)
    (src_ret_params:= src_ret_params d)
    (src_precompile_params:= src_precompile_params d)
    (dest_pv:= dest_pv d)
    (dest_heap_ptr:= dest_heap_ptr d)
    (dest_fat_ptr:= dest_fat_ptr d)
    (dest_meta_params:= dest_meta_params d)
  .

  Inductive instruction: Type :=
  | OpInvalid
  | OpNoOp
  | OpSpAdd       (in1: src_pv) (ofs: imm_in)  (* encoded as NoOp with $out_1$ *)
  | OpSpSub       (in1: src_pv) (ofs: imm_in) (* encoded as NoOp with $in_1$ *)

  | OpJump        (dest: src_pv)
  | OpAnd         (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (flags:mod_set_flags)
  | OpOr          (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (flags:mod_set_flags)
  | OpXor         (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (flags:mod_set_flags)
  | OpAdd         (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (flags:mod_set_flags)
  | OpSub         (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (flags:mod_set_flags)

  | OpShl         (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (flags:mod_set_flags)
  | OpShr         (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (flags:mod_set_flags)
  | OpRol         (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (flags:mod_set_flags)
  | OpRor         (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (flags:mod_set_flags)

  | OpMul         (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (out2: dest_pv) (flags:mod_set_flags)
  | OpDiv         (in1: src_pv) (in2: src_pv)  (out1: dest_pv) (out2: dest_pv) (flags:mod_set_flags)
  | OpNearCall    (in1: src_nearcall_params) (dest: imm_in) (handler: imm_in)
  | OpFarCall     (enc: src_farcall_params) (dest: src_pv) (handler: imm_in) (is_static:bool) (is_shard_provided: bool)
  | OpMimicCall   (enc: src_farcall_params) (dest: src_pv) (handler: imm_in) (is_static:bool) (is_shard_provided: bool)
  | OpDelegateCall(enc: src_farcall_params) (dest: src_pv) (handler: imm_in) (is_static:bool) (is_shard_provided: bool)

  | OpNearRet
  | OpNearRetTo     (label: code_address)
  | OpFarRet        (args: src_ret_params)

  | OpNearRevert
  | OpNearRevertTo  (label: code_address)
  | OpFarRevert     (args: src_ret_params)
  | OpNearPanicTo   (label: code_address)
  | OpPanic

  | OpPtrAdd      (in1: src_fat_ptr) (in2: src_pv)  (out: dest_fat_ptr)
  | OpPtrSub      (in1: src_fat_ptr) (in2: src_pv)  (out: dest_fat_ptr)
  | OpPtrShrink   (in1: src_fat_ptr) (in2: src_pv)  (out: dest_fat_ptr)
  | OpPtrPack     (in1: src_fat_ptr) (in2: src_pv)  (out: dest_pv)


  | OpLoad        (ptr: src_heap_ptr) (res: dest_pv) (mem:data_page_type)
  | OpLoadInc     (ptr: src_heap_ptr) (res: dest_pv) (mem:data_page_type) (inc_ptr: dest_heap_ptr)
  | OpStore       (ptr: src_heap_ptr) (val: src_pv)  (mem:data_page_type)
  | OpStoreInc    (ptr: src_heap_ptr) (val: src_pv)  (mem:data_page_type) (inc_ptr: dest_heap_ptr)


  | OpLoadPointer     (ptr: src_fat_ptr)  (res: dest_pv)
  | OpLoadPointerInc  (ptr: src_fat_ptr)  (res: dest_pv) (inc_ptr: dest_fat_ptr)


  | OpContextThis                                   (out: dest_pv)
  | OpContextCaller                                 (out: dest_pv)
  | OpContextCodeAddress                            (out: dest_pv)
  | OpContextMeta                                   (out: dest_meta_params)
  | OpContextErgsLeft                               (out: dest_pv)
  | OpContextSp                                     (out: dest_pv)
  | OpContextGetContextU128                         (out: dest_pv)
  | OpContextSetContextU128        (in1: src_pv)
  | OpContextSetErgsPerPubdataByte (in1: src_pv)
  | OpContextIncrementTxNumber


  | OpSLoad          (in1: src_pv)                  (out: dest_pv)
  | OpSStore         (in1: src_pv) (in2: src_pv)
  | OpToL1Message    (in1: src_pv) (in2: src_pv)                   (is_first: bool)
  | OpEvent          (in1: src_pv) (in2: src_pv)                   (is_first: bool)
  | OpPrecompileCall (in1: src_precompile_params) (ergs:src_pv)    (out: dest_pv)
  .

End Functor.





#[global]
  Canonical Structure decoded: descr :=
  let src := in_any in
  let dest := out_any in
  {|
    src_pv := src;
    src_fat_ptr :=src;
    src_heap_ptr :=src;
    src_farcall_params := src;
    src_nearcall_params := src;
    src_ret_params := src;
    src_precompile_params := src;
    dest_pv := dest;
    dest_heap_ptr := dest;
    dest_fat_ptr := dest;
    dest_meta_params := dest;
  |}.

Section InstructionMapper.

  Notation state_rel S OP V := (S -> S -> OP -> V -> Prop).

  Record relate_st {S} {A B: descr}: Type :=
    {
      mf_src_pv : state_rel S (src_pv A) (src_pv B);
      mf_src_fat_ptr: state_rel S (src_fat_ptr A) (src_fat_ptr B);
      mf_src_heap_ptr: state_rel S (src_heap_ptr A) (src_heap_ptr B);
      mf_src_farcall_params: state_rel S (src_farcall_params A) (src_farcall_params B);
      mf_src_nearcall_params: state_rel S (src_nearcall_params A) (src_nearcall_params B);
      mf_src_ret_params: state_rel S (src_ret_params A) (src_ret_params B);
      mf_src_precompile_params: state_rel S (src_precompile_params A) (src_precompile_params B);
      mf_dest_pv: state_rel S (dest_pv A) (dest_pv B);
      mf_dest_heap_ptr: state_rel S (dest_heap_ptr A) (dest_heap_ptr B);
      mf_dest_fat_ptr : state_rel S (dest_fat_ptr  A) (dest_fat_ptr  B);
      mf_dest_meta_params: state_rel S (dest_meta_params A) (dest_meta_params B);
    }.

  Generalizable Variables s i o imm fs.

  Context {S A B} (m:@relate_st S A B)
      (mf_src_pv := mf_src_pv m)
      (mf_src_fat_ptr := mf_src_fat_ptr m)
      (mf_src_heap_ptr := mf_src_heap_ptr m)
      (mf_src_farcall_params := mf_src_farcall_params m)
      (mf_src_nearcall_params := mf_src_nearcall_params m)
      (mf_src_ret_params := mf_src_ret_params m)
      (mf_src_precompile_params := mf_src_precompile_params m)
      (mf_dest_pv := mf_dest_pv m)
      (mf_dest_heap_ptr := mf_dest_heap_ptr m)
      (mf_dest_fat_ptr := mf_dest_fat_ptr m)
      (mf_dest_meta_params := mf_dest_meta_params m)
  .


  Inductive ins_srelate :  S -> S -> @instruction A -> @instruction B -> Prop :=
  |sim_noop: forall s, ins_srelate s s OpNoOp OpNoOp
  |sim_invalid: forall s, ins_srelate s s OpInvalid OpInvalid
  |sim_sp_add: `(
                   mf_src_pv s0 s1 i1 i1' ->
                   ins_srelate s0 s1 (OpSpAdd i1 imm1) (OpSpAdd i1' imm1)
                 )
  |sim_sp_sub: `(
                   mf_src_pv s0 s1 i1 i1' ->
                   ins_srelate s0 s1 (OpSpSub i1 imm1) (OpSpSub i1' imm1)
                 )
  |sim_jump: `(
                 mf_src_pv s0 s1 i1 i1' ->
                 ins_srelate s0 s1 (OpJump i1) (OpJump i1')
               )
  |sim_and: `(
                mf_src_pv s0 s1 i1 i1' ->
                mf_src_pv s1 s2 i2 i2' ->
                mf_dest_pv s2 s3 o1 o1' ->
                ins_srelate s0 s3 (OpAnd i1 i2 o1 fs) (OpAnd i1' i2' o1'  fs)
              )
  |sim_or: `(
               mf_src_pv s0 s1 i1 i1' ->
               mf_src_pv s1 s2 i2 i2' ->
               mf_dest_pv s2 s3 o1 o1' ->
               ins_srelate s0 s3 (OpOr i1 i2 o1  fs) (OpOr i1' i2' o1'  fs)
             )
  |sim_xor: `(
                mf_src_pv s0 s1 i1 i1' ->
                mf_src_pv s1 s2 i2 i2' ->
                mf_dest_pv s2 s3 o1 o1' ->
                ins_srelate s0 s3 (OpXor i1 i2 o1  fs) (OpXor i1' i2' o1'  fs)
              )
  |sim_add: `(
                mf_src_pv s0 s1 i1 i1' ->
                mf_src_pv s1 s2 i2 i2' ->
                mf_dest_pv s2 s3 o1 o1' ->
                ins_srelate s0 s3 (OpAdd i1 i2 o1  fs) (OpAdd i1' i2' o1'  fs)
              )
  |sim_sub: `(
                mf_src_pv s0 s1 i1 i1' ->
                mf_src_pv s1 s2 i2 i2' ->
                mf_dest_pv s2 s3 o1 o1' ->
                ins_srelate s0 s3 (OpSub i1 i2 o1  fs) (OpSub i1' i2' o1'  fs)
              )
  |sim_shl: `(
                mf_src_pv s0 s1 i1 i1' ->
                mf_src_pv s1 s2 i2 i2' ->
                mf_dest_pv s2 s3 o1 o1' ->
                ins_srelate s0 s3 (OpShl i1 i2 o1 fs) (OpShl i1' i2' o1' fs)
              )
  |sim_shr: `(
                mf_src_pv s0 s1 i1 i1' ->
                mf_src_pv s1 s2 i2 i2' ->
                mf_dest_pv s2 s3 o1 o1' ->
                ins_srelate s0 s3 (OpShr i1 i2 o1 fs) (OpShr i1' i2' o1' fs)
              )
  |sim_rol: `(
                mf_src_pv s0 s1 i1 i1' ->
                mf_src_pv s1 s2 i2 i2' ->
                mf_dest_pv s2 s3 o1 o1' ->
                ins_srelate s0 s3 (OpRol i1 i2 o1 fs) (OpRol i1' i2' o1' fs)
              )
  |sim_ror: `(
                mf_src_pv s0 s1 i1 i1' ->
                mf_src_pv s1 s2 i2 i2' ->
                mf_dest_pv s2 s3 o1 o1' ->
                ins_srelate s0 s3 (OpRor i1 i2 o1 fs) (OpRor i1' i2' o1' fs)
              )
  |sim_PtrAdd: `(
                   mf_src_fat_ptr s0 s1 i1 i1' ->
                   mf_src_pv s1 s2 i2 i2' ->
                   mf_dest_fat_ptr s2 s3 o1 o1' ->
                   ins_srelate s0 s3 (OpPtrAdd i1 i2 o1) (OpPtrAdd i1' i2' o1')
                 )
  |sim_PtrSub: `(
                   mf_src_fat_ptr s0 s1 i1 i1' ->
                   mf_src_pv s1 s2 i2 i2' ->
                   mf_dest_fat_ptr s2 s3 o1 o1' ->
                   ins_srelate s0 s3 (OpPtrSub i1 i2 o1) (OpPtrSub i1' i2' o1')
                 )
  |sim_PtrShrink: `(
                      mf_src_fat_ptr s0 s1 i1 i1' ->
                      mf_src_pv s1 s2 i2 i2' ->
                      mf_dest_fat_ptr s2 s3 o1 o1' ->
                      ins_srelate s0 s3 (OpPtrShrink i1 i2 o1) (OpPtrShrink i1' i2' o1')
                    )
  |sim_PtrPack: `(
                    mf_src_fat_ptr s0 s1 i1 i1' ->
                    mf_src_pv s1 s2 i2 i2' ->
                    mf_dest_pv s2 s3 o1 o1' ->
                    ins_srelate s0 s3 (OpPtrPack i1 i2 o1) (OpPtrPack i1' i2' o1')
                  )
  |sim_mul: `(
                mf_src_pv s0 s1 i1 i1' ->
                mf_src_pv s1 s2 i2 i2' ->
                mf_dest_pv s2 s3 o1 o1' ->
                mf_dest_pv s3 s4 o2 o2' ->
                ins_srelate s0 s4 (OpMul i1 i2 o1 o2  fs) (OpMul i1' i2' o1' o2' fs )
              )
  |sim_div: `(
                mf_src_pv s0 s1 i1 i1' ->
                mf_src_pv s1 s2 i2 i2' ->
                mf_dest_pv s2 s3 o1 o1' ->
                mf_dest_pv s3 s4 o2 o2' ->
                ins_srelate s0 s4 (OpDiv i1 i2 o1 o2  fs) (OpDiv i1' i2' o1' o2'  fs)
              )
  |sim_nearcall: `(
                     forall dest handler,
                       mf_src_nearcall_params s0 s1 i1 i1' ->
                       ins_srelate s0 s1 (OpNearCall i1 dest handler) (OpNearCall i1' dest handler)
                   )
  |sim_farcall: `(
                    forall handler static shard,
                      mf_src_farcall_params s0 s1 i1 i1' ->
                      mf_src_pv s1 s2 i2 i2' ->
                      ins_srelate s0 s2 (OpFarCall i1 i2 handler static shard) (OpFarCall i1' i2' handler static shard)
                  )
  |sim_mimiccall: `(
                      forall handler static shard,
                        mf_src_farcall_params s0 s1 i1 i1' ->
                        mf_src_pv s1 s2 i2 i2' ->
                        ins_srelate s0 s2 (OpMimicCall i1 i2 handler static shard) (OpMimicCall i1' i2' handler static shard)
                    )
  |sim_delegatecall: `(
                         forall handler static shard,
                           mf_src_farcall_params s0 s1 i1 i1' ->
                           mf_src_pv s1 s2 i2 i2' ->
                           ins_srelate s0 s2(OpDelegateCall i1 i2 handler static shard) (OpDelegateCall i1' i2' handler static shard)
                       )
  |sim_nearret: forall s, ins_srelate s s OpNearRet OpNearRet
  |sim_nearrevert: forall s, ins_srelate s s OpNearRevert OpNearRevert
  |sim_nearpanic: forall s, ins_srelate s s OpPanic OpPanic
  |sim_nearretto: forall s l, ins_srelate s s (OpNearRetTo l) (OpNearRetTo l)
  |sim_nearrevertto: forall s l, ins_srelate s s (OpNearRevertTo l) (OpNearRevertTo l)
  |sim_nearpanicto: forall s l, ins_srelate s s (OpNearPanicTo l) (OpNearPanicTo l)
  |sim_farret: `(
                   mf_src_ret_params s0 s1 i1 i1' ->
                   ins_srelate s0 s1 (OpFarRet i1) (OpFarRet i1')
                 )
  |sim_farrevert: `(
                      mf_src_ret_params s0 s1 i1 i1' ->
                      ins_srelate s0 s1 (OpFarRevert i1) (OpFarRevert i1')
                    )
  |sim_load:`( forall type,
          mf_src_heap_ptr s0 s1 i1 i1' ->
          mf_dest_pv s1 s2 o1 o1' ->
          ins_srelate s0 s2 (OpLoad i1 o1 type) (OpLoad  i1' o1' type)
      )
  |sim_loadptr:`(
        mf_src_fat_ptr s0 s1 i1 i1' ->
        mf_dest_pv s1 s2 o1 o1' ->
        ins_srelate s0 s2 (OpLoadPointer i1 o1) (OpLoadPointer i1' o1' )
      )
  |sim_loadinc:`( forall type,
          mf_src_heap_ptr s0 s1 i1 i1' ->
          mf_dest_pv s1 s2 o1 o1' ->
          mf_dest_heap_ptr s2 s3 o2 o2' ->
          ins_srelate s0 s3 (OpLoadInc i1 o1 type o2) (OpLoadInc i1' o1' type o2')
      )
  |sim_loadptrinc:`(
        mf_src_fat_ptr s0 s1 i1 i1' ->
        mf_dest_pv s1 s2 o1 o1' ->
        mf_dest_fat_ptr s2 s3 o2 o2' ->
        ins_srelate s0 s3 (OpLoadPointerInc i1 o1 o2) (OpLoadPointerInc i1' o1' o2')
      )
  |sim_store:`( forall type,
          mf_src_heap_ptr s0 s1 i1 i1' ->
          mf_src_pv s1 s2 i2 i2' ->
          mf_dest_pv s2 s3 o1 o1' ->
          ins_srelate s0 s3 (OpStore i1 i2 type) (OpStore i1' i2' type)
      )
  |sim_storeinc:`( forall type,
          mf_src_heap_ptr s0 s1 i1 i1' ->
          mf_src_pv s1 s2 i2 i2' ->
          mf_dest_heap_ptr s2 s3 o1 o1' ->
          ins_srelate s0 s3 (OpStoreInc i1 i2 type o1) (OpStoreInc i1' i2' type o1')
      )
  |sim_OpContextThis: `(
                         mf_dest_pv s0 s1 o1 o1' ->
                         ins_srelate s0 s1 (OpContextThis o1) (OpContextThis o1'))
  |sim_OpContextCaller: `(
                           mf_dest_pv s0 s1 o1 o1' ->
                           ins_srelate s0 s1 (OpContextCaller o1) (OpContextCaller o1'))
  |sim_OpContextCodeAddress: `(
                                mf_dest_pv s0 s1 o1 o1' ->
                                ins_srelate s0 s1 (OpContextCodeAddress o1) (OpContextCodeAddress o1'))
  |sim_OpContextMeta: `(
                         mf_dest_meta_params s0 s1 o1 o1' ->
                         ins_srelate s0 s1 (OpContextMeta o1) (OpContextMeta o1'))
  |sim_OpContextErgsLeft: `(
                             mf_dest_pv s0 s1 o1 o1' ->
                             ins_srelate s0 s1 (OpContextErgsLeft o1) (OpContextErgsLeft o1'))
  |sim_OpContextSp: `(
                       mf_dest_pv s0 s1 o1 o1' ->
                       ins_srelate s0 s1 (OpContextSp o1) (OpContextSp o1'))
  |sim_OpContextGetContextU128: `(
                                   mf_dest_pv s0 s1 o1 o1' ->
                                   ins_srelate s0 s1 (OpContextGetContextU128 o1) (OpContextGetContextU128 o1'))
  |sim_OpContextSetContextU128: `(
                                   mf_src_pv s0 s1 i1 i1' ->
                                   ins_srelate s0 s1 (OpContextSetContextU128 i1) (OpContextSetContextU128 i1'))
  |sim_OpContextSetErgsPerPubdataByte: `(
                                          mf_src_pv s0 s1 i1 i1' ->
                                          ins_srelate s0 s1 (OpContextSetErgsPerPubdataByte i1) (OpContextSetErgsPerPubdataByte i1'))
  |sim_OpContextIncrementTxNumber: `(
                                      mf_dest_pv s0 s1 o1 o1' ->
                                      ins_srelate s0 s1 (OpContextIncrementTxNumber ) (OpContextIncrementTxNumber ))
  |sim_OpSLoad: `(
                   mf_src_pv s0 s1 i1 i1' ->
                   mf_dest_pv s1 s2 o1 o1' ->
                   ins_srelate s0 s2 (OpSLoad i1 o1) (OpSLoad i1' o1'))
  |sim_OpSStore: `(
                    mf_src_pv s0 s1 i1 i1' ->
                    mf_src_pv s1 s2 i2 i2' ->
                    ins_srelate s0 s2 (OpSStore i1 i2) (OpSStore i1' i2'))
  |sim_OpToL1Message: `(forall first,
                           mf_src_pv s0 s1 i1 i1' ->
                           mf_src_pv s1 s2 i2 i2' ->
                           ins_srelate s0 s2 (OpToL1Message i1 i2 first) (OpToL1Message i1' i2' first))
  |sim_OpEvent: `(forall first,
                     mf_src_pv s0 s1 i1 i1' ->
                     mf_src_pv s1 s2 i2 i2' ->
                     ins_srelate s0 s2 (OpEvent i1 i2 first) (OpEvent i1' i2' first))
  |sim_OpPrecompileCall: `(
                            mf_src_precompile_params s0 s1 i1 i1' ->
                            mf_src_pv s1 s2 i2 i2' ->
                            mf_dest_pv s2 s3 o1 o1' ->
                            ins_srelate s0 s3 (OpPrecompileCall i1 i2 o1) (OpPrecompileCall i1' i2' o1'))
  .

  Generalizable No Variables.
End InstructionMapper.
