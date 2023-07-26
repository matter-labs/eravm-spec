Require Addressing Common Memory Predication.

Import Addressing Common Memory Predication Flags.

(**
- This file describes the syntax of assembly instructions.
 - The instruction semantic is described in a different place; see all files in [%sem] module.
 - This is a high-level instruction set, not an encoding-aware low-level machine
   instruction set. The distinction between them is of convenience: while in encoded machine instructions some fields are only occasionally used, the instructions from this set only contain used fields.

   For example, `xor`, `or`, and `and` bitwise operations are represented by
   three distinct instructions in this set; however, they are encoded using the
   same opcode and different modifiers. *)
Section Instructions.
  (** # Common instruction modifiers

Modifiers alter the meaning of instruction.

Two modifiers are commonly encountered:

  1. `swap`: if an instruction has two input operands, this modifier swaps
    them.
   *)
  Inductive mod_swap := Swap | NoSwap.

  Definition apply_swap {T} (md: mod_swap) (a b:T) : T*T :=
    match md with
    | NoSwap => (a,b)
    | Swap => (b,a)
    end.

  (**
  For example, take an instruction

  [%OpSub a b c NoSwap PreserveFlags]

  It computes $a - b$ and stores the result to $c$.

  Adding `swap` modifier will change the syntax as follows:

  [%OpSub a b c Swap PreserveFlags]

  The new meaning with `swap` modifier is to compute $b-a$.

  In binary operations the first input operand usually supports more
  sophisticated address modes: it can be e.g. fetched from stack, whereas the
  second one can only be fetched from a GPR.

  2. `set_flags`: if set, an instruction is allowed to change [%gs_flags]. If
    cleared, the instruction will not alter the flags.
   *)
  Inductive mod_set_flags := SetFlags | PreserveFlags.

  Definition apply_set_flags (md: mod_set_flags) (f f':flags_state) : flags_state :=
    match md with
    | SetFlags => f'
    | PreserveFlags => f
    end.

  Section InstructionFormat.
    Structure instruction_descr: Type := {
        in_any_pv: Type;
        out_any_pv: Type;
        in_reg_pv: Type;
        out_reg_pv: Type;
        out_reg_fatptr: Type;
        out_reg_heapptr: Type;
        in_reg_farcall_abi: Type;
        in_reg_nearcall_abi: Type;
        in_reg_ret_abi: Type;
        in_reg_fatptr: Type;
        in_regimm_heapptr: Type;
      }.
    Context {descr: instruction_descr}
      (in_any_pv := in_any_pv descr)
      (out_any_pv := out_any_pv descr)
      (in_reg_pv := in_reg_pv descr)
      (out_reg_pv := out_reg_pv descr)
      (out_reg_fatptr:= out_reg_fatptr descr)
      (out_reg_heapptr := out_reg_heapptr descr)
      (in_reg_farcall_abi := in_reg_farcall_abi descr)
      (in_reg_nearcall_abi := in_reg_nearcall_abi descr)
      (in_reg_ret_abi := in_reg_ret_abi descr)
      (in_reg_fatptr := in_reg_fatptr descr)
      (in_regimm_heapptr := in_regimm_heapptr descr).
    (** # EraVM high-level instruction set

The definition [%instruction] enumerates all available instructions, omitting
the predicate (see [%instruction_predicated] and [%Predication]). This is a
higher-level instruction set. Then the [%instruction_predicated] is encoded into
a fixed instruction format, then it is serialized to 256-bit words.
     *)
    Inductive instruction: Type :=
    | OpInvalid
    | OpNoOp
    | OpModSP       (in1: in_any_pv) (out1: out_any_pv)
    | OpJump        (dest: in_any_pv)
    | OpAnd         (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv)                 (swap:mod_swap) (flags:mod_set_flags)
    | OpOr          (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv)                 (swap:mod_swap) (flags:mod_set_flags)
    | OpXor         (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv)                 (swap:mod_swap) (flags:mod_set_flags)
    | OpAdd         (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv)                 (swap:mod_swap) (flags:mod_set_flags)
    | OpSub         (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv)                 (swap:mod_swap) (flags:mod_set_flags)

    | OpShl         (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv)                                 (flags:mod_set_flags)
    | OpShr         (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv)                                 (flags:mod_set_flags)
    | OpRol         (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv)                                 (flags:mod_set_flags)
    | OpRor         (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv)                                 (flags:mod_set_flags)

    | OpMul         (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv) (out2: out_reg_pv) (swap:mod_swap) (flags:mod_set_flags)
    | OpDiv         (in1: in_any_pv) (in2: in_reg_pv)  (out1: out_any_pv) (out2: out_reg_pv) (swap:mod_swap) (flags:mod_set_flags)
    | OpNearCall    (in1: in_reg_nearcall_abi) (dest: imm_in) (handler: imm_in)
    | OpFarCall     (enc: in_reg_farcall_abi) (dest: in_reg_pv) (handler: imm_in) (is_static:bool) (is_shard_provided: bool)
    | OpMimicCall   (enc: in_reg_farcall_abi) (dest: in_reg_pv) (handler: imm_in) (is_static:bool) (is_shard_provided: bool)
    | OpDelegateCall(enc: in_reg_farcall_abi) (dest: in_reg_pv) (handler: imm_in) (is_static:bool) (is_shard_provided: bool)


    | OpNearRet
    | OpNearRetTo      (label: code_address)
    | OpFarRet         (args: in_reg_ret_abi)

    | OpNearRevert
    | OpNearRevertTo(label: code_address)
    | OpFarRevert   (args: in_reg_ret_abi)
    | OpNearPanicTo (label: code_address)
    | OpPanic

    | OpPtrAdd      (in1: in_any_pv) (in2: in_reg_pv)  (out: out_any_pv) (swap:mod_swap)
    | OpPtrSub      (in1: in_any_pv) (in2: in_reg_pv)  (out: out_any_pv) (swap:mod_swap)
    | OpPtrShrink   (in1: in_any_pv) (in2: in_reg_pv)  (out: out_any_pv) (swap:mod_swap)
    | OpPtrPack     (in1: in_any_pv) (in2: in_reg_pv)  (out: out_any_pv) (swap:mod_swap)


    | OpLoad        (ptr: in_regimm_heapptr) (res: out_reg_pv) (mem:data_page_type)
    | OpLoadInc     (ptr: in_regimm_heapptr) (res: out_reg_pv) (mem:data_page_type) (inc_ptr: out_reg_heapptr)
    | OpStore       (ptr: in_regimm_heapptr) (val: in_reg_pv)  (mem:data_page_type)
    | OpStoreInc    (ptr: in_regimm_heapptr) (val: in_reg_pv)  (mem:data_page_type) (inc_ptr: out_reg_heapptr)


    | OpLoadPointer     (ptr: in_reg_fatptr)  (res: out_reg_pv)
    | OpLoadPointerInc  (ptr: in_reg_fatptr)  (res: out_reg_pv) (inc_ptr: out_reg_fatptr)


    | OpContextThis                                   (out: out_reg_pv)
    | OpContextCaller                                 (out: out_reg_pv)
    | OpContextCodeAddress                            (out: out_reg_pv)
    | OpContextMeta                                   (out: out_reg_pv)
    | OpContextErgsLeft                               (out: out_reg_pv)
    | OpContextSp                                     (out: out_reg_pv)
    | OpContextGetContextU128                         (out: out_reg_pv)
    | OpContextSetContextU128        (in1: in_reg_pv)
    | OpContextSetErgsPerPubdataByte (in1: in_reg_pv)
    | OpContextIncrementTxNumber


    | OpSLoad          (in1: in_reg_pv)                  (out: out_reg_pv)
    | OpSStore         (in1: in_reg_pv) (in2: in_reg_pv)
    | OpToL1Message    (in1: in_reg_pv) (in2: in_reg_pv)                   (is_first: bool)
    | OpEvent          (in1: in_reg_pv) (in2: in_reg_pv)                   (is_first: bool)
    | OpPrecompileCall (in1: in_reg_pv)                  (out: out_reg_pv)
    .

  End InstructionFormat.
  (** ## Predicated instruction

The type [%instruction_predicated] defines the predicated instruction.
These are the instructions stored on [%code_page]s.

Such instruction contains two parts:

- opcode-specific part;
- execution conditions, describing under which conditions (flags) the instruction will be executed. *)
  #[global]
    Canonical Structure
    instruction_stored: instruction_descr :=
    {|
      in_any_pv := in_any;
      out_any_pv := out_any;
      in_reg_pv := in_reg;
      out_reg_pv := out_reg;
      in_reg_farcall_abi := in_reg;
      in_reg_nearcall_abi := in_reg;
      in_reg_ret_abi := in_reg;
      in_regimm_heapptr := in_regimm;
      out_reg_fatptr := out_reg;
      out_reg_heapptr := out_reg;
      in_reg_fatptr := in_reg;
    |}.


  Record instruction_predicated: Type :=
    Ins {
        ins_spec: @instruction instruction_stored;
        ins_cond: predicate;
      }.

  (** Invalid instruction. It is a default value on code memory pages. See
  [%code_page]. It is parameterized by an instruction type for convenience of
  defining it. *)

  Definition instruction_invalid : instruction_predicated :=
    {|
      ins_spec := OpInvalid;
      ins_cond:= IfAlways
    |}.

End Instructions.

(** A helper definition to specialize a code page with a (just defined) instruction type. *)
Definition code_page : Type := code_page instruction_invalid.

Section InstructionMapper.
  
  Record instruction_mapper {A B: instruction_descr}: Type :=
    {
      f_in_any_pv : in_any_pv A -> in_any_pv B -> Prop;
      f_in_reg_pv : in_reg_pv A -> in_reg_pv B -> Prop;
      f_in_reg_farcall_abi : in_reg_farcall_abi A -> in_reg_farcall_abi B -> Prop;
      f_in_reg_nearcall_abi : in_reg_nearcall_abi A -> in_reg_nearcall_abi B -> Prop;
      f_in_reg_ret_abi : in_reg_ret_abi A -> in_reg_ret_abi B -> Prop;
      f_in_regimm_heapptr : in_regimm_heapptr A -> in_regimm_heapptr B -> Prop;
      f_in_reg_fatptr : in_reg_fatptr A -> in_reg_fatptr B -> Prop;

      f_out_reg_pv : out_reg_pv A -> out_reg_pv B -> Prop;
      f_out_any_pv : out_any_pv A -> out_any_pv B -> Prop;
      f_out_reg_fatptr : out_reg_fatptr A -> out_reg_fatptr B -> Prop;
      f_out_reg_heapptr : out_reg_heapptr A -> out_reg_heapptr B -> Prop;
    }.

  Generalizable Variables i o swap fs.

  Inductive instruction_rmap {A B} m:  @instruction A -> @instruction B -> Prop :=
  | im_noop: instruction_rmap m OpNoOp OpNoOp
  | im_invalid: instruction_rmap m OpInvalid OpInvalid
  | im_modsp: `(
                  f_in_any_pv m i1 i1' ->
                  f_out_any_pv m o1 o1' ->
                  instruction_rmap m (OpModSP i1 o1) (OpModSP i1' o1')
                )
  | im_jump: `(
                 f_in_any_pv m i1 i1' ->
                 instruction_rmap m (OpJump i1) (OpJump i1')
               )
  | im_and: `(
                f_in_any_pv m i1 i1' ->
                f_in_reg_pv m i2 i2' ->
                f_out_any_pv m o1 o1' ->
                instruction_rmap m (OpAnd i1 i2 o1 swap fs) (OpAnd i1' i2' o1' swap fs)
              )
  | im_or: `(
               f_in_any_pv m i1 i1' ->
               f_in_reg_pv m i2 i2' ->
               f_out_any_pv m o1 o1' ->
               instruction_rmap m (OpOr i1 i2 o1 swap fs) (OpOr i1' i2' o1' swap fs)
             )
  | im_xor: `(
                f_in_any_pv m i1 i1' ->
                f_in_reg_pv m i2 i2' ->
                f_out_any_pv m o1 o1' ->
                instruction_rmap m (OpXor i1 i2 o1 swap fs) (OpXor i1' i2' o1' swap fs)
              )
  | im_add: `(
                f_in_any_pv m i1 i1' ->
                f_in_reg_pv m i2 i2' ->
                f_out_any_pv m o1 o1' ->
                instruction_rmap m (OpAdd i1 i2 o1 swap fs) (OpAdd i1' i2' o1' swap fs)
              )
  | im_sub: `(
                f_in_any_pv m i1 i1' ->
                f_in_reg_pv m i2 i2' ->
                f_out_any_pv m o1 o1' ->
                instruction_rmap m (OpSub i1 i2 o1 swap fs) (OpSub i1' i2' o1' swap fs)
              )
  | im_shl: `(
                f_in_any_pv m i1 i1' ->
                f_in_reg_pv m i2 i2' ->
                f_out_any_pv m o1 o1' ->
                instruction_rmap m (OpShl i1 i2 o1 fs) (OpShl i1' i2' o1' fs)
              )
  | im_shr: `(
                f_in_any_pv m i1 i1' ->
                f_in_reg_pv m i2 i2' ->
                f_out_any_pv m o1 o1' ->
                instruction_rmap m (OpShr i1 i2 o1 fs) (OpShr i1' i2' o1' fs)
              )
  | im_rol: `(
                f_in_any_pv m i1 i1' ->
                f_in_reg_pv m i2 i2' ->
                f_out_any_pv m o1 o1' ->
                instruction_rmap m (OpRol i1 i2 o1 fs) (OpRol i1' i2' o1' fs)
              )
  | im_ror: `(
                f_in_any_pv m i1 i1' ->
                f_in_reg_pv m i2 i2' ->
                f_out_any_pv m o1 o1' ->
                instruction_rmap m (OpRor i1 i2 o1 fs) (OpRor i1' i2' o1' fs)
              )
  | im_PtrAdd: `(
                   f_in_any_pv m i1 i1' ->
                   f_in_reg_pv m i2 i2' ->
                   f_out_any_pv m o1 o1' ->
                   instruction_rmap m (OpPtrAdd i1 i2 o1 fs) (OpPtrAdd i1' i2' o1' fs)
                 )
  | im_PtrSub: `(
                   f_in_any_pv m i1 i1' ->
                   f_in_reg_pv m i2 i2' ->
                   f_out_any_pv m o1 o1' ->
                   instruction_rmap m (OpPtrSub i1 i2 o1 fs) (OpPtrSub i1' i2' o1' fs)
                 )
  | im_PtrShrink: `(
                      f_in_any_pv m i1 i1' ->
                      f_in_reg_pv m i2 i2' ->
                      f_out_any_pv m o1 o1' ->
                      instruction_rmap m (OpPtrShrink i1 i2 o1 fs) (OpPtrShrink i1' i2' o1' fs)
                    )
  | im_PtrPack: `(
                    f_in_any_pv m i1 i1' ->
                    f_in_reg_pv m i2 i2' ->
                    f_out_any_pv m o1 o1' ->
                    instruction_rmap m (OpPtrPack i1 i2 o1 fs) (OpPtrPack i1' i2' o1' fs)
                  )
  | im_mul: `(
                f_in_any_pv m i1 i1' ->
                f_in_reg_pv m i2 i2' ->
                f_out_any_pv m o1 o1' ->
                f_out_reg_pv m o2 o2' ->
                instruction_rmap m (OpMul i1 i2 o1 o2 swap fs) (OpMul i1' i2' o1' o2' swap fs)
              )
  | im_div: `(
                f_in_any_pv m i1 i1' ->
                f_in_reg_pv m i2 i2' ->
                f_out_any_pv m o1 o1' ->
                f_out_reg_pv m o2 o2' ->
                instruction_rmap m (OpDiv i1 i2 o1 o2 swap fs) (OpDiv i1' i2' o1' o2' swap fs)
              )
  | im_nearcall: `(
                     forall dest handler,
                       f_in_reg_nearcall_abi m i1 i1' ->
                       instruction_rmap m (OpNearCall i1 dest handler) (OpNearCall i1' dest handler)
                   )
  | im_farcall: `(
                    forall handler static shard,
                      f_in_reg_farcall_abi m i1 i1' ->
                      f_in_reg_pv m i2 i2' ->
                      instruction_rmap m (OpFarCall i1 i2 handler static shard) (OpFarCall i1' i2' handler static shard)
                  )
  | im_mimiccall: `(
                      forall handler static shard,
                        f_in_reg_farcall_abi m i1 i1' ->
                        f_in_reg_pv m i2 i2' ->
                        instruction_rmap m (OpMimicCall i1 i2 handler static shard) (OpMimicCall i1' i2' handler static shard)
                    )
  | im_delegatecall: `(
                         forall handler static shard,
                           f_in_reg_farcall_abi m i1 i1' ->
                           f_in_reg_pv m i2 i2' ->
                           instruction_rmap m (OpDelegateCall i1 i2 handler static shard) (OpDelegateCall i1' i2' handler static shard)
                       )
  | im_nearret: instruction_rmap m OpNearRet OpNearRet
  | im_nearrevert: instruction_rmap m OpNearRevert OpNearRevert
  | im_nearpanic: instruction_rmap m OpPanic OpPanic
  | im_nearretto: forall l, instruction_rmap m (OpNearRetTo l) (OpNearRetTo l)
  | im_nearrevertto: forall l, instruction_rmap m (OpNearRevertTo l) (OpNearRevertTo l)
  | im_nearpanicto: forall l, instruction_rmap m (OpNearPanicTo l) (OpNearPanicTo l)
  | im_farret: `(
                   f_in_reg_ret_abi m i1 i1' ->
                   instruction_rmap m (OpFarRet i1) (OpFarRet i1')
                 )
  | im_farrevert: `(
                      f_in_reg_ret_abi m i1 i1' ->
                      instruction_rmap m (OpFarRevert i1) (OpFarRevert i1')
                    )
  | im_load:`( forall type,
          f_in_regimm_heapptr m i1 i1' ->
          f_out_reg_pv m o1 o1' ->
          instruction_rmap m (OpLoad i1 o1 type) (OpLoad  i1' o1' type)
      )
  | im_loadptr:`(
        f_in_reg_fatptr m i1 i1' ->
        f_out_reg_pv m o1 o1' ->
        instruction_rmap m (OpLoadPointer i1 o1) (OpLoadPointer i1' o1' )
      )
  | im_loadinc:`( forall type,
          f_in_regimm_heapptr m i1 i1' ->
          f_out_reg_pv m o1 o1' ->
          f_out_reg_heapptr m o2 o2' ->
          instruction_rmap m (OpLoadInc i1 o1 type o2) (OpLoadInc i1' o1' type o2')
      )
  | im_loadptrinc:`(
        f_in_reg_fatptr m i1 i1' ->
        f_out_reg_pv m o1 o1' ->
        f_out_reg_fatptr m o2 o2' ->
        instruction_rmap m (OpLoadPointerInc i1 o1 o2) (OpLoadPointerInc i1' o1' o2')
      )
  | im_store:`( forall type,
          f_in_regimm_heapptr m i1 i1' ->
          f_in_reg_pv m i2 i2' ->
          f_out_reg_pv m o1 o1' ->
          instruction_rmap m (OpStore i1 i2 type) (OpStore i1' i2' type)
      )
  | im_storeinc:`( forall type,
          f_in_regimm_heapptr m i1 i1' ->
          f_in_reg_pv m i2 i2' ->
          f_out_reg_heapptr m o1 o1' ->
          instruction_rmap m (OpStoreInc i1 i2 type o1) (OpStoreInc i1' i2' type o1')
      )
  |im_OpContextThis: `(
                         f_out_reg_pv m o1 o1' ->
                         instruction_rmap m (OpContextThis o1) (OpContextThis o1'))
  |im_OpContextCaller: `(
                           f_out_reg_pv m o1 o1' ->
                           instruction_rmap m (OpContextCaller o1) (OpContextCaller o1'))
  |im_OpContextCodeAddress: `(
                                f_out_reg_pv m o1 o1' ->
                                instruction_rmap m (OpContextCodeAddress o1) (OpContextCodeAddress o1'))
  |im_OpContextMeta: `(
                         f_out_reg_pv m o1 o1' ->
                         instruction_rmap m (OpContextMeta o1) (OpContextMeta o1'))
  |im_OpContextErgsLeft: `(
                             f_out_reg_pv m o1 o1' ->
                             instruction_rmap m (OpContextErgsLeft o1) (OpContextErgsLeft o1'))
  |im_OpContextSp: `(
                       f_out_reg_pv m o1 o1' ->
                       instruction_rmap m (OpContextSp o1) (OpContextSp o1'))
  |im_OpContextGetContextU128: `(
                                   f_out_reg_pv m o1 o1' ->
                                   instruction_rmap m (OpContextGetContextU128 o1) (OpContextGetContextU128 o1'))
  |im_OpContextSetContextU128: `(
                                   f_in_reg_pv m i1 i1' ->
                                   instruction_rmap m (OpContextSetContextU128 i1) (OpContextSetContextU128 i1'))
  |im_OpContextSetErgsPerPubdataByte: `(
                                          f_in_reg_pv m i1 i1' ->
                                          instruction_rmap m (OpContextSetErgsPerPubdataByte i1) (OpContextSetErgsPerPubdataByte i1'))
  |im_OpContextIncrementTxNumber: `(
                                      f_out_reg_pv m o1 o1' ->
                                      instruction_rmap m (OpContextIncrementTxNumber ) (OpContextIncrementTxNumber ))
  |im_OpSLoad: `(
                   f_in_reg_pv m i1 i1' ->
                   f_out_reg_pv m o1 o1' ->
                   instruction_rmap m (OpSLoad i1 o1) (OpSLoad i1' o1'))
  |im_OpSStore: `(
                    f_in_reg_pv m i1 i1' ->
                    f_in_reg_pv m i2 i2' ->
                    instruction_rmap m (OpSStore i1 i2) (OpSStore i1' i2'))
  |im_OpToL1Message: `(forall first,
                           f_in_reg_pv m i1 i1' ->
                           f_in_reg_pv m i2 i2' ->
                           instruction_rmap m (OpToL1Message i1 i2 first) (OpToL1Message i1' i2' first))
  |im_OpEvent: `(forall first,
                     f_in_reg_pv m i1 i1' ->
                     f_in_reg_pv m i2 i2' ->
                     instruction_rmap m (OpEvent i1 i2 first) (OpEvent i1' i2' first))
  |im_OpPrecompileCall: `(
                            f_in_reg_pv m i1 i1' ->
                            f_out_reg_pv m o1 o1' ->
                            instruction_rmap m (OpPrecompileCall i1 o1) (OpPrecompileCall i1' o1'))
  .


  Context {A B C} (m1: @instruction_mapper A B) (m2: @instruction_mapper B C).

  Definition rmap_comp {A B C} (m1: @instruction_mapper A B) (m2: @instruction_mapper B C) : @instruction_mapper A C :=
    {|
      f_in_any_pv := rcomp m1.(f_in_any_pv) m2.(f_in_any_pv);
      f_in_reg_pv := rcomp m1.(f_in_reg_pv) m2.(f_in_reg_pv);
      f_in_reg_farcall_abi := rcomp m1.(f_in_reg_farcall_abi) m2.(f_in_reg_farcall_abi);
      f_in_reg_nearcall_abi := rcomp m1.(f_in_reg_nearcall_abi) m2.(f_in_reg_nearcall_abi);
      f_in_reg_ret_abi := rcomp m1.(f_in_reg_ret_abi) m2.(f_in_reg_ret_abi);
      f_in_regimm_heapptr := rcomp m1.(f_in_regimm_heapptr) m2.(f_in_regimm_heapptr);
      f_in_reg_fatptr := rcomp m1.(f_in_reg_fatptr) m2.(f_in_reg_fatptr);
      f_out_reg_pv := rcomp m1.(f_out_reg_pv) m2.(f_out_reg_pv);
      f_out_any_pv := rcomp m1.(f_out_any_pv) m2.(f_out_any_pv);
      f_out_reg_fatptr := rcomp m1.(f_out_reg_fatptr) m2.(f_out_reg_fatptr);
      f_out_reg_heapptr := rcomp m1.(f_out_reg_heapptr) m2.(f_out_reg_heapptr);
    |}
  .

End InstructionMapper.
