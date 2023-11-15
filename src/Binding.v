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
    PointerErasure
    PrimitiveValue
    State.
Import
  ABI
    FatPointerABI
    Addressing
    Addressing.Coercions
    CallStack
    Coder
    Core
    GPR
    isa.CoreSet
    MemoryOps
    Pointer
    PointerErasure
    PrimitiveValue
    State
    Types.

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
  {|
    src_pv := @primitive_value Core.word;
    src_fat_ptr := option (@primitive_value (u128 * fat_ptr_nullable));
    src_heap_ptr := option (@primitive_value (u224 * heap_ptr));
    src_farcall_params := option (@primitive_value FarCallABI.params);
    src_nearcall_params := option (@primitive_value (u224 * NearCallABI.params));
    src_ret_params := option (@primitive_value FarRetABI.params);
    src_precompile_params := option (@primitive_value PrecompileParametersABI.params);
    dest_pv := @primitive_value Core.word;
    dest_heap_ptr := option (@primitive_value (u224 * heap_ptr) );
    dest_fat_ptr := option (@primitive_value (u128 * fat_ptr_nullable) );
    dest_meta_params := option (@primitive_value (MetaParametersABI.params ));
  |}
  .

  (**
Knowing the call stack, memory pages and registers are enough to bind any value appearing in [%CoreInstructionSet]; additionally, kernel mode affects it: pointer erasure only happens in user mode.
   *)
  Record binding_state := mk_bind_st {
                              bs_is_kernel_mode: bool;
                              bs_cs: State.callstack;
                              bs_regs: regs_state;
                              bs_mem: State.memory;
                            }.

  Inductive bind_any_src: binding_state -> binding_state -> in_any -> @primitive_value word -> Prop :=
  | bind_any_src_apply: forall regs (mem:State.memory) (cs cs':State.callstack) (op:in_any) (v:@primitive_value word) (is_k: bool),
      load _ regs cs mem op (cs', v) ->
      bind_any_src (mk_bind_st is_k cs regs mem) (mk_bind_st is_k cs' regs mem) op v.

  (** To bind a [%src_pv] type of instruction operand, load its
  value and apply the effects of [%RelSpPop] addressing mode.
  Additionally, if the instruction expects an integer, but gets a pointer with a
  tag, the pointer erasure happens (since v.1.4.1).
   *)

  Inductive bind_src: binding_state -> binding_state -> in_any -> @primitive_value word -> Prop :=
  | bind_src_int_apply: forall regs (mem:State.memory) (cs cs':State.callstack) (op:in_any) (v:word) (is_k: bool),
      bind_any_src (mk_bind_st is_k cs regs mem) (mk_bind_st is_k cs' regs mem) op (IntValue v) ->
      bind_src (mk_bind_st is_k cs regs mem) (mk_bind_st is_k cs' regs mem) op (IntValue v)

  | bind_src_ptr_apply: forall regs (mem:State.memory) (cs cs':State.callstack) (op:in_any) (v v':word)
                          (decoded decoded_erased: fat_ptr_nullable)
                          (encoded_erased high128: u128)
                          (is_k: bool),
      bind_any_src (mk_bind_st is_k cs regs mem) (mk_bind_st is_k cs' regs mem) op (PtrValue v) ->

      Some (high128, decoded) = decode_fat_ptr_word v ->
      decoded_erased = fat_ptr_nullable_erase is_k decoded ->
      Some encoded_erased = encode_fat_ptr decoded ->
      v' = high128 ## encoded_erased ->

      bind_src (mk_bind_st is_k cs regs mem) (mk_bind_st is_k cs' regs mem) op (IntValue v')
  .

  (** To bind a [%dest_pv] type of instruction operand, store its
  value and apply the effects of [%RelSpPush] addressing mode. *)
  Inductive bind_dest: binding_state -> binding_state -> out_any -> primitive_value  -> Prop :=
  | bind_dest_apply: forall regs mem cs regs' mem' cs' op val is_k,
      store _ regs cs mem op val (regs', mem', cs') ->
      bind_dest (mk_bind_st is_k cs regs mem) (mk_bind_st is_k cs' regs' mem') op val.

  (** To bind [%src_fat_ptr] or any other compound value encoded in a binary form,  bind both the encoded and decoded value. *)
  Inductive bind_fat_ptr: binding_state -> binding_state -> in_any -> option (@primitive_value (u128 * fat_ptr_nullable)) -> Prop :=
  | bind_fat_ptr_apply : forall op v s s' decoded high128,
      bind_src s s' op v ->
      Some (high128, decoded) = decode_fat_ptr_word v.(value) ->
      bind_fat_ptr s s' op (Some (PtrValue (high128, decoded)))
  .

  Inductive bind_heap_ptr: binding_state -> binding_state -> in_any -> option (@primitive_value (u224 * heap_ptr)) -> Prop :=
  | bind_heap_ptr_apply : forall op v s s' decoded,
      bind_src s s' op v ->
      Some decoded = decode_heap_ptr v.(value) ->
      bind_heap_ptr s s' op (Some (IntValue decoded)).

  Inductive bind_farcall_params: binding_state -> binding_state -> in_any -> option (@primitive_value FarCallABI.params) -> Prop :=
  | bind_farcall_params_apply : forall op v s s' decoded tag,
      bind_src s s' op v ->
      Some decoded = FarCallABI.coder.(decode) v.(value) ->
      bind_farcall_params s s' op (Some (mk_pv tag (decoded)))
  .

  Inductive bind_nearcall_params: binding_state -> binding_state -> in_any -> option (@primitive_value (u224* NearCallABI.params)) -> Prop :=
  | bind_nearcall_params_apply : forall op v s s' decoded tag,
      bind_src s s' op v ->
      Some decoded = NearCallABI.decode_word v.(value) ->
      bind_nearcall_params s s' op (Some (mk_pv tag decoded)).

  Inductive bind_farret_params: binding_state -> binding_state -> in_any -> option (@primitive_value FarRetABI.params) -> Prop :=
  | bind_farret_params_apply : forall op v s s' decoded tag,
      bind_src s s' op v ->
      Some decoded = FarRetABI.coder.(decode) v.(value) ->
      bind_farret_params s s' op (Some (mk_pv tag decoded)).

  Inductive bind_precompile_params: binding_state -> binding_state -> in_any -> option (@primitive_value PrecompileParametersABI.params) -> Prop :=
  | bind_precompile_params_apply : forall op v s s' decoded tag,
      bind_src s s' op v ->
      Some decoded = PrecompileParametersABI.ABI.(decode) v.(value) ->
      bind_precompile_params s s' op (Some (mk_pv tag decoded)).

  Inductive bind_dest_fat_ptr: binding_state -> binding_state -> out_any ->
                               option (@primitive_value (u128 * fat_ptr_nullable) ) -> Prop :=
  | bind_dest_fat_ptr_apply: forall s s' op encoded ptr (high128:u128),
      bind_dest s s' op (PtrValue encoded) ->
      encode_fat_ptr_word high128 ptr = Some encoded ->
      bind_dest_fat_ptr s s' op (Some (PtrValue (high128, ptr)))
  .

  Inductive bind_dest_heap_ptr: binding_state -> binding_state -> out_any -> option (@primitive_value (u224 * heap_ptr) ) -> Prop :=
  | bind_dest_heap_ptr_apply: forall s s' op (encoded:word) high224 hptr,
      bind_dest s s' op (IntValue encoded) ->
      encode_heap_ptr_word high224 hptr = Some encoded ->
      bind_dest_heap_ptr s s' op (Some (IntValue (high224, hptr)))
  .


  Inductive bind_dest_meta_params: binding_state -> binding_state -> out_any -> option (@primitive_value (MetaParametersABI.params)) -> Prop :=
  | bind_dest_meta_params_apply: forall s s' op encoded params,
      bind_dest s s' op (IntValue encoded) ->
      MetaParametersABI.coder.(encode) params = Some encoded ->
      bind_dest_meta_params s s' op (Some (IntValue params))
  .

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
  Definition get_binding_state_ts (s: transient_state) : binding_state :=
    {|
      bs_is_kernel_mode := in_kernel_mode (gs_callstack s);
      bs_regs := gs_regs s;
      bs_mem  := gs_pages s;
      bs_cs   := gs_callstack s;
    |}.

  #[local]
  Definition get_binding_state (s: state) : binding_state := get_binding_state_ts s.

  Inductive relate_transient_states (P: binding_state -> binding_state -> Prop): transient_state -> transient_state -> Prop :=
  | rts_apply:
    forall ts1 ts2,
      P (get_binding_state_ts ts1) (get_binding_state_ts ts2)->
      relate_transient_states P ts1 ts2.

  #[local]
  Definition merge_binding_transient_state: binding_state -> transient_state -> transient_state :=
    fun bs s1 =>
      match bs with
      | mk_bind_st _ cs regs gmem => s1
                                   <| gs_regs      := regs |>
                                   <| gs_pages     := gmem |>
                                   <| gs_callstack := cs   |>
      end.

  #[local]
  Definition merge_binding_state : state -> binding_state -> state :=
    fun s1 bs =>
      match bs with
      | mk_bind_st _ cs regs gmem => s1 <| gs_transient ::= merge_binding_transient_state bs |>
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
