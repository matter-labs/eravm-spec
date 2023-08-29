Require Coder Ergs Pointer GPR MemoryManagement.

Import ssreflect ssreflect.ssrfun ssreflect.ssrbool ssreflect.eqtype ssreflect.tuple zmodp.
Import Core Common Coder Bool GPR Ergs Memory MemoryManagement Pointer.


#[local]
Definition coder := @coder word.


(** # Application binary interface (ABI)

This section details the serialization and deserialization formats for compound
instruction arguments.


Currently, they are not described in details, but introduced axiomatically.

The description from Rust VM implementation is described here:
https://github.com/matter-labs/zkevm_opcode_defs/blob/v1.4.1/src/definitions/abi

## Fat pointers *)
Module FatPointer.
  Axiom ABI  : @coder fat_ptr.

  Definition decode_fat_ptr (w:word) : option fat_ptr := ABI.(decode) w.

  Definition decode_heap_ptr (w:word) : option heap_ptr :=
    match decode_fat_ptr w with
    | Some (mk_fat_ptr _ (mk_ptr _ offset)) =>
        Some (mk_hptr offset)
    | None => None
   end.

  Definition decode_span (w:word) : option span :=
    match decode_fat_ptr w with
    | Some (mk_fat_ptr _ (mk_ptr s _ ))=> Some s
    | None => None
   end.

  Definition encode_fat_ptr (fp: fat_ptr) : word := ABI.(encode) fp.

End FatPointer.


(** ## Near call *)
Module NearCall.

  Record params: Type :=
    mk_params {
        ergs_passed: u32;
      }.

  Axiom ABI: @coder params.

End NearCall.


(** ## Far returns *)
Module FarRet.
  Record params := mk_params {
                           forwarded_memory :> fwd_memory
                          }.
  Axiom ABI: @coder params.
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

  Axiom ABI: @coder params.

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

  Axiom ABI: @coder params.

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
  Axiom ABI: @coder params.

End PrecompileParameters.
