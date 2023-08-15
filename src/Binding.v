From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require
  ABI
    Addressing
    CallStack
    Core
    Coder
    GPR
    isa.CoreSet
    Pointer
    PrimitiveValue
    State.
Import
  ABI
    ABI.FatPointer
    Addressing
    Addressing.Coercions
    CallStack
    Coder
    Core
    GPR
    isa.CoreSet
    MemoryOps
    Pointer
    PrimitiveValue
    State.

Section OperandBinding.

  (**
# Binding operands in core instructions

The instructions from [%CoreInstructionSet] are parameterized with an instance of [%descr], specifying the exact types of their operands. This allows for [%instruction] definition to be reused:

- the [%instruction decoded] are instructions decoded from [%Assembly.asm_instruction]. They contain descriptions of operand sources and destinations, e.g. register or various memory locations.
- the [%instruction bound] are instructions that contain the values fetched, stored, and with decoding/encoding already performed. It allows to bind these values equationally inside the spec clauses such as [%step_add].

The rest of this section is technical; refer to [%bind_fat_ptr] and similar
predicates to see how the compound instruction arguments are encoded and
decoded for small step relations, e.g. [%step_ptradd] for [%OpPtrAdd].
   *)
  #[global]
    Canonical Structure bound: descr :=
  let pv := @primitive_value word in
  {|
    src_pv := pv;
    src_fat_ptr := option fat_ptr * pv ;
    src_heap_ptr := option heap_ptr * pv;
    src_farcall_params := option ABI.FarCall.params * pv;
    src_nearcall_params := option ABI.NearCall.params * pv;
    src_ret_params := option ABI.FarRet.params * pv;
    src_precompile_params := option ABI.PrecompileParameters.params * pv;
    dest_pv := pv;
    dest_heap_ptr := heap_ptr * pv;
    dest_fat_ptr := fat_ptr * pv;
    dest_meta_params := ABI.MetaParameters.params * pv;
  |}
  .

  (**
Knowing the call stack, memory pages and registers are enough to bind any value appearing in [%CoreInstructionSet].
   *)
  Record binding_state := mk_bind_st {
                              bs_cs: State.callstack;
                              bs_regs: regs_state;
                              bs_mem: State.memory;
                            }.

  (** To bind a [%src_pv] type of instruction operand, load its
  value and apply the effects of [%RelSpPop] addressing mode. *)
  Inductive bind_src: binding_state -> binding_state -> in_any -> @primitive_value word -> Prop :=
  | bind_src_apply: forall regs (mem:State.memory) (cs cs':State.callstack) (op:in_any) (v:@primitive_value word),
      load _ regs cs mem op (cs', v) ->
      bind_src (mk_bind_st cs regs mem) (mk_bind_st cs' regs mem) op v.

  (** To bind a [%dest_pv] type of instruction operand, store its
  value and apply the effects of [%RelSpPush] addressing mode. *)
  Inductive bind_dest: binding_state -> binding_state -> out_any -> primitive_value  -> Prop :=
  | bind_dest_apply: forall regs mem cs regs' mem' cs' op val,
      store _ regs cs mem op val (regs', mem', cs') ->
      bind_dest (mk_bind_st cs regs mem) (mk_bind_st cs' regs' mem') op val.

  (** To bind [%src_fat_ptr] or any other compound value encoded in a binary form,  bind both the encoded and decoded value. *)
  Inductive bind_fat_ptr: binding_state -> binding_state -> in_any -> option fat_ptr * primitive_value -> Prop :=
  | bind_fat_ptr_apply : forall op v s s' decoded,
      bind_src s s' op v ->
      decoded = decode_fat_ptr v.(value) ->
      bind_fat_ptr s s' op (decoded, v).

  Inductive bind_heap_ptr: binding_state -> binding_state -> in_any -> option heap_ptr * primitive_value -> Prop :=
  | bind_heap_ptr_apply : forall op v s s' decoded,
      bind_src s s' op v ->
      decoded = decode_heap_ptr v.(value) ->
      bind_heap_ptr s s' op (decoded, v).

  Inductive bind_farcall_params: binding_state -> binding_state -> in_any -> option ABI.FarCall.params * primitive_value -> Prop :=
  | bind_farcall_params_apply : forall op v s s' decoded,
      bind_src s s' op v ->
      decoded = ABI.FarCall.ABI.(decode) v.(value) ->
      bind_farcall_params s s' op (decoded, v).

  Inductive bind_nearcall_params: binding_state -> binding_state -> in_any -> option ABI.NearCall.params * primitive_value -> Prop :=
  | bind_nearcall_params_apply : forall op v s s' decoded,
      bind_src s s' op v ->
      decoded = ABI.NearCall.ABI.(decode) v.(value) ->
      bind_nearcall_params s s' op (decoded, v).

  Inductive bind_farret_params: binding_state -> binding_state -> in_any -> option ABI.FarRet.params * primitive_value -> Prop :=
  | bind_farret_params_apply : forall op v s s' decoded,
      bind_src s s' op v ->
      decoded = ABI.FarRet.ABI.(decode) v.(value) ->
      bind_farret_params s s' op (decoded, v).

  Inductive bind_precompile_params: binding_state -> binding_state -> in_any -> option ABI.PrecompileParameters.params * primitive_value -> Prop :=
  | bind_precompile_params_apply : forall op v s s' decoded,
      bind_src s s' op v ->
      decoded = ABI.PrecompileParameters.ABI.(decode) v.(value) ->
      bind_precompile_params s s' op (decoded, v).

  (** Implementation note: Using "decode" in bindings is a weaker version of "encode".
 Instead of postulating that `encoded` is the precise result of encoding the
 pointer, we postulate that it will be decoded to the required pointer value. It
 means, that if decoder ignores a part of the value, we can still bind it with
 some relation. This is used e.g. in [%OpPtrAdd] that has to preserve 128 most significant bits. *)
  Inductive bind_dest_fat_ptr: binding_state -> binding_state -> out_any -> fat_ptr * primitive_value -> Prop :=
  | bind_dest_fat_ptr_apply: forall s s' op encoded ptr,
      bind_dest s s' op (PtrValue encoded) ->
      decode_fat_ptr encoded = Some ptr ->
      bind_dest_fat_ptr s s' op (ptr, PtrValue encoded).

  Inductive bind_dest_heap_ptr: binding_state -> binding_state -> out_any -> heap_ptr * primitive_value -> Prop :=
  | bind_dest_heap_ptr_apply: forall s s' op encoded ptr,
      bind_dest s s' op (PtrValue encoded) ->
      decode_heap_ptr encoded = Some ptr ->
      bind_dest_heap_ptr s s' op (ptr, PtrValue encoded).

  Inductive bind_dest_meta_params: binding_state -> binding_state -> out_any ->
                                   ABI.MetaParameters.params * primitive_value -> Prop :=
  | bind_dest_meta_params_apply: forall s s' op encoded meta_params,
      bind_dest s s' op (IntValue encoded) ->
      ABI.MetaParameters.ABI.(decode) encoded = Some meta_params ->
      bind_dest_meta_params s s' op (meta_params, IntValue encoded).

  Definition bind_relation :=
    {|
      mf_src_pv := bind_src;
      mf_src_fat_ptr := bind_fat_ptr;
      mf_src_heap_ptr := bind_heap_ptr;
      mf_src_farcall_params := bind_farcall_params;
      mf_src_nearcall_params := bind_nearcall_params;
      mf_src_ret_params := bind_farret_params;
      mf_src_precompile_params := bind_precompile_params;
      mf_dest_pv := bind_dest;
      mf_dest_fat_ptr := bind_dest_fat_ptr;
      mf_dest_heap_ptr := bind_dest_heap_ptr;
      mf_dest_meta_params := bind_dest_meta_params;
    |}.

  #[local]
  Definition get_binding_state (s: state) : binding_state :=
    {|
      bs_regs := gs_regs s;
      bs_mem  := gs_pages s;
      bs_cs   := gs_callstack s;
    |}.

  Inductive relate_transient_states (P: binding_state -> binding_state -> Prop): transient_state -> transient_state -> Prop :=
  | rts_apply:
    forall r1 r2 m1 m2 c1 c2 ctx flags,
      P (mk_bind_st c1 r1 m1 ) (mk_bind_st c1 r1 m1) ->
      relate_transient_states P (mk_transient_state flags r1 m1 c1 ctx) (mk_transient_state flags r2 m2 c2 ctx).

  #[local]
  Definition merge_binding_transient_state: binding_state -> transient_state -> transient_state :=
    fun bs s1 =>
      match bs with
      | mk_bind_st cs regs gmem => s1
                                    <| gs_regs      := regs |>
                                                         <| gs_pages     := gmem |>
                                                                              <| gs_callstack := cs   |>
      end.

  #[local]
  Definition merge_binding_state : state -> binding_state -> state :=
    fun s1 bs =>
      match bs with
      | mk_bind_st cs regs gmem => s1 <| gs_transient ::= merge_binding_transient_state bs |>
      end.

  #[local]
  Definition bind_operands_binding_state (s1 s2: binding_state) :
    @instruction decoded -> @instruction bound -> Prop :=
    ins_srelate bind_relation s1 s2 .

  (** The definition [%bind_operands] relates two [%transient_state]s before and after binding, and two instructions:

- $i_1$ is a decoded instruction obtained by applying [%to_core] to [%Assembly.asm_instruction];
- $i_2$ is a bound instruction where fetching and storing values, as well as encoding and decoding are abstracted.

The values of operands in $i_2$ can be further bound by relations, see e.g. [%step_add].

   *)
  #[global]
  Definition bind_operands (s1 s2:transient_state) (i1: @instruction decoded) (i2: @instruction bound) : Prop :=
    relate_transient_states (fun bs1 bs2 => bind_operands_binding_state bs1 bs2 i1 i2) s1 s2.

End OperandBinding.
