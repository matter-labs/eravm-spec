Require Coder Ergs Pointer GPR MemoryManagement.

Import ssreflect ssreflect.ssrfun ssreflect.ssrbool ssreflect.eqtype ssreflect.tuple zmodp.
Import Core Common Coder Bool GPR Ergs Memory MemoryManagement Pointer.


(** # Application binary interface (ABI)

This section details the serialization and deserialization formats for compound
instruction arguments.


Currently, they are not described in details, but introduced axiomatically.

The description from Rust VM implementation is described here:
https://github.com/matter-labs/zkevm_opcode_defs/blob/v1.4.1/src/definitions/abi

## Fat pointers *)
Module FatPointer.
  Axiom ABI  : @coder u128 fat_ptr_nullable.

  Definition decode_fat_ptr (w:u128) : option fat_ptr_nullable := ABI.(decode) w.

  Definition decode_fat_ptr_word (w:word) : option (u128 * fat_ptr_nullable) :=
    let (high128, low128) := split2 128 128 w in
    match decode_fat_ptr low128 with
    | Some fpn => Some (high128, fpn)
    | _ => None
    end
  .

  Definition decode_heap_ptr (w:word) : option (u224 * heap_ptr) :=
    let (msbs, ofs) := split2 _ 32 w in
    Some (msbs, mk_hptr ofs).

  Definition encode_heap_ptr (h:heap_ptr) : option u32 :=
    Some (hp_addr h)
  .

  Definition encode_heap_ptr_word (high224: u224) (h:heap_ptr) : option word :=
    match encode_heap_ptr h with
    | Some hpenc => Some (high224 ## hpenc)
    | _ => None
    end
  .
  Definition encode_fat_ptr (fp: fat_ptr_nullable) : u128 := ABI.(encode) fp.
  Definition encode_fat_ptr_word (high_bytes: u128) (fp: fat_ptr_nullable) : word :=
    high_bytes ## encode_fat_ptr fp.

End FatPointer.


(** ## Near call *)
Module NearCall.

  Record params: Type :=
    mk_params {
        ergs_passed: u32;
      }.

  Axiom ABI: @coder word params.

End NearCall.


(** ## Far returns *)
Module FarRet.
  Record params := mk_params {
                           forwarded_memory :> fwd_memory
                          }.
  Axiom ABI: @coder word params.
  Axiom ABI_decode_zero: ABI.(decode) word0 = Some (mk_params (ForwardNewFatPointer Heap span_empty)).
End FarRet.

(** ## Far call *)
Module FarCall.
  Import FatPointer.

  Record params :=
    mk_params {
        fwd_memory: fwd_memory;
        ergs_passed: ergs;
        shard_id: shard_id;
        constructor_call: bool;
        to_system: bool;
      }.

  Axiom ABI: @coder word params.

End FarCall.


Module MetaParameters.

  Record params :=
    mk_params {
        ergs_per_pubdata_byte: ergs;
        heap_size: mem_address;
        aux_heap_size: mem_address;
        this_shard_id: shard_id;
        caller_shard_id: shard_id;
        code_shard_id: shard_id;
      }.

  Axiom ABI: @coder word params.

End MetaParameters.

Module PrecompileParameters.

  Record params :=
    mk_params
      {
        input_memory_offset: mem_address;
        input_memory_length: mem_address;
        output_memory_offset: mem_address;
        output_memory_length: mem_address;
        per_precompile_interpreted: u64;
        memory_page_to_read: page_id;
        memory_page_to_write: page_id;
        precompile_interpreted_data: u64;
      }.

  Definition params_eqn (x y: params) : bool :=
    (x.(input_memory_offset) == y.(input_memory_offset)) &&
      (x.(input_memory_length) == y.(input_memory_length)) &&
      (x.(output_memory_offset) == y.(output_memory_offset)) &&
      (x.(output_memory_length) == y.(output_memory_length)) &&
      (x.(per_precompile_interpreted) == y.(per_precompile_interpreted)) &&
      (x.(memory_page_to_read) == y.(memory_page_to_read)) &&
      (x.(memory_page_to_write) == y.(memory_page_to_write)) &&
      (x.(precompile_interpreted_data) == y.(precompile_interpreted_data)).

  Lemma params_eqnP : Equality.axiom params_eqn.
  Proof.
    move => x y.
    unfold params_eqn.
    destruct x,y =>//=.
    repeat match goal with
             [ |- context [(?x == ?y)] ] =>
               let Hf := fresh "H" in
               destruct (x == y) eqn: Hf; try rewrite Hf
           end =>//=; constructor; auto;
      repeat match goal with [ H: (?x == ?y) = true |- _] => move: H => /eqP -> end;
      try injection; intros; subst;
      repeat match goal with [ H: (?x == ?x) = false |- _] => rewrite eq_refl in H end =>//=.
    - constructor.
  Qed.
  Canonical params_eqMixin := EqMixin params_eqnP.
  Canonical params_eqType := Eval hnf in EqType _ params_eqMixin.
  Axiom ABI: @coder word params.

End PrecompileParameters.
